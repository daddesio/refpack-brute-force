/*
** RefPack brute-force compressor
** Authors: Fatbag (2015)
** License: Public domain (no warranties)
*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <errno.h>

struct output_state {
	uint32_t distance; /* distance from the origin */
	uint8_t command[4]; /* command that brought us here from the
		previous state */
};

static __inline void set_cmd_2(uint8_t command[4], uint32_t pdl, uint32_t rdl,
	uint32_t rdo)
{
	command[0] = (((rdo-1)>>8)<<5) | ((rdl-3)<<2) | pdl;
	command[1] = (rdo-1)&0xFF;
}

static __inline void set_cmd_3(uint8_t command[4], uint32_t pdl, uint32_t rdl,
	uint32_t rdo)
{
	command[0] = 0x80 | (rdl-4);
	command[1] = (pdl<<6) | ((rdo-1)>>8);
	command[2] = (rdo-1)&0xFF;
}

static __inline void set_cmd_4(uint8_t command[4], uint32_t pdl, uint32_t rdl,
	uint32_t rdo)
{
	command[0] = 0xc0 | (((rdo-1)>>16)<<4) | (((rdl-5)>>8)<<2) | pdl;
	command[1] = ((rdo-1)>>8)&0xFF;
	command[2] = (rdo-1)&0xFF;
	command[3] = (rdl-5)&0xFF;
}

static __inline void set_cmd_1(uint8_t command[4], uint32_t pdl)
{
	command[0] = 0xe0 | ((pdl>>2)-1);
}

static __inline void get_command(const uint8_t command[4],
	uint32_t *__restrict type, uint32_t *__restrict pdl,
	uint32_t *__restrict rdl, uint32_t *__restrict rdo)
{
	if (!(command[0] & 0x80)) {
		/* 2-byte command */
		*type = 2;
		*pdl = command[0] & 0x03;
		*rdl = ((command[0] >> 2) & 0x07) + 3;
		*rdo = ((command[0] & 0x60) << 3) + command[1] + 1;
	} else if (!(command[0] & 0x40)) {
		/* 3-byte command */
		*type = 3;
		*pdl = command[1] >> 6;
		*rdl = (command[0] & 0x3f) + 4;
		*rdo = ((command[1] & 0x3f) << 8) + command[2] + 1;
	} else if (!(command[0] & 0x20)) {
		/* 4-byte command */
		*type = 4;
		*pdl = command[0] & 0x03;
		*rdl = ((command[0] & 0x0c) << 6) + command[3] + 5;
		*rdo = ((command[0] & 0x10) << 12) + (command[1] << 8)
			+ command[2] + 1;
	} else {
		/* 1-byte command */
		*type = 1;
		*pdl = ((command[0] & 0x1f) + 1) << 2;
		*rdl = 0;
		*rdo = 0;
	}
}

static int refpack_brute_force_compress(const uint8_t *indata, size_t insize,
	uint8_t **outdata_out, size_t *outsize_out)
{
	struct output_state *states;
	uint8_t *outdata;
	size_t outsize;
	uint32_t type, pdl, rdl, rdo;
	uint32_t dist;
	uint32_t i, j;

	if (insize <= 3) {
		outdata = malloc(6 + insize);
		if (!outdata)
			return -1;

		outdata[0] = 0x10;
		outdata[1] = 0xfb;
		outdata[2] = 0x00;
		outdata[3] = 0x00;
		outdata[4] = insize;
		outdata[5] = 0xfc | insize;
		if (insize)
			memcpy(outdata+6, indata, insize);

		*outdata_out = outdata;
		*outsize_out = 6 + insize;
		return 0;
	}

	states = malloc((insize + 1) * sizeof(struct output_state));
	if (!states)
		return -1;

	states[0].distance = 0;
	for (i = 1; i <= insize; i++)
		states[i].distance = UINT32_MAX;

	/* At this point, states 0 through 3 are fully optimized. */

	for (i = 0; i <= insize-3; i++) {
		/* At this point, states 0 through i+2 (inclusive) are
		** fully optimized. */

		rdo = 0;
		for (rdl = 3; rdl <= insize - i && rdl <= 1028; rdl++) {
			/* Find a reference which would output the same data as
			** indata+i through indata+i+rdl-1. Using a reference
			** near the front of the sliding window is always
			** preferential to farther back. */
			if (rdl == 3 || indata[i-rdo+rdl-1] !=
				indata[i+rdl-1]) {
				/* The reference we used for rdl=x doesn't work
				** anymore for rdl=x+1. We need to check farther
				** back for a new reference. */
				for (rdo++; rdo <= i && rdo <= 131072 &&
					memcmp(indata+i-rdo, indata+i, rdl)
					!= 0; rdo++);
				if (rdo > i || rdo > 131072)
					break;
			}

			/* Optimize state i+rdl using either:
			** (*) state i with pdl=0,
			** (*) state i-1 with pdl=1,
			** (*) state i-2 with pdl=2, or
			** (*) state i-3 with pdl=3,
			** whichever has the least cost to state i+rdl.
			** (States i-3 through i are all fully optimized at this
			** point.) */
			pdl = 0;
			dist = states[i].distance;
			for (j = 1; j <= i && j <= 3; j++) {
				if (states[i-j].distance <= UINT32_MAX - j
					&& states[i-j].distance + j < dist) {
					pdl = j;
					dist = states[i-j].distance + j;
				}
			}

			/* Using a 2-byte command, if possible, is always less
			** costly than using the 3-byte or 4-byte command; and
			** the 3-byte command is always less costly than the
			** 4-byte command. */
			if (rdo <= 1024 && rdl <= 10) {
				/* 2-byte command */
				if (dist > UINT32_MAX - 2
					|| dist + 2 >= states[i+rdl].distance)
					continue;
				states[i+rdl].distance = dist + 2;
				set_cmd_2(states[i+rdl].command, pdl, rdl, rdo);
			} else if (rdo <= 16384 && rdl >= 4 && rdl <= 67) {
				/* 3-byte command */
				if (dist > UINT32_MAX - 3
					|| dist + 3 >= states[i+rdl].distance)
					continue;
				states[i+rdl].distance = dist + 3;
				set_cmd_3(states[i+rdl].command, pdl, rdl, rdo);
			} else if (rdl >= 5) {
				/* 4-byte command */
				if (dist > UINT32_MAX - 4
					|| dist + 4 >= states[i+rdl].distance)
					continue;
				states[i+rdl].distance = dist + 4;
				set_cmd_4(states[i+rdl].command, pdl, rdl, rdo);
			}
		}

		for (pdl = 4; pdl <= insize - i && pdl <= 112; pdl += 4) {
			/* 1-byte command: optimize state i+pdl with rdl=0. */
			if (1 + pdl > UINT32_MAX - states[i].distance)
				break;
			dist = states[i].distance + 1 + pdl;
			if (dist < states[i+pdl].distance) {
				states[i+pdl].distance = dist;
				set_cmd_1(states[i+pdl].command, pdl);
			}
		}
	}

	/* Add the stop command directly after either state insize, insize-1,
	** insize-2, or insize-3 (using pld=0, 1, 2, or 3 resp.), whichever is
	** cheapest. Note that we are not adding the stop command to the states
	** array. */
	pdl = 0;
	dist = states[insize].distance;
	for (i = 1; i <= 3; i++) {
		if (states[insize-i].distance <= UINT32_MAX - i
			&& states[insize-i].distance + i < dist) {
			pdl = i;
			dist = states[insize-i].distance + i;
		}
	}

	/* Calculate the final size, for the RefPack header (5), plus the
	** non-stop commands and the stop command's proceeding data (dist),
	** plus the stop command's opcode (1). */
	if (5 + 1 > UINT32_MAX - dist) {
		free(states);
		return -1;
	}
	outsize = dist + 5 + 1;

	outdata = malloc(outsize);
	if (!outdata) {
		free(states);
		return -1;
	}

	/* Output the shortest path to the stop command, iterating from the end
	** to the start. */
	outdata[outsize-1-pdl] = 0xfc | pdl; /* stop command */
	memcpy(outdata+outsize-pdl, indata+insize-pdl, pdl);
	i = insize - pdl;
	while (i != 0) {
		get_command(states[i].command, &type, &pdl, &rdl, &rdo);
		dist = states[i].distance;
		memcpy(outdata+5+dist-pdl-type, states[i].command, type);
		memcpy(outdata+5+dist-pdl, indata+i-rdl-pdl, pdl);
		i -= rdl, i -= pdl;
	}

	/* Free the state data. */
	free(states);

	/* Output the RefPack header. */
	outdata[0] = 0x10;
	outdata[1] = 0xfb;
	outdata[2] = (insize>>16)&0xFF;
	outdata[3] = (insize>>8)&0xFF;
	outdata[4] = insize&0xFF;

	*outdata_out = outdata;
	*outsize_out = outsize;
	return 0;
}

int main(int argc, char *argv[])
{
	FILE *fd;
	long ret;
	uint8_t *indata, *outdata;
	size_t insize, outsize;

	if (argc != 3) {
		printf("Usage: refpack_brute_force INFILE OUTFILE\n");
		return EXIT_SUCCESS;
	}

	fd = fopen(argv[1], "rb");
	if (!fd) {
		fprintf(stderr, "Error: failed to open input file for reading"
			" (%s)\n", strerror(errno));
		return EXIT_FAILURE;
	}

	if (fseek(fd, 0, SEEK_END) != 0 || (ret = ftell(fd)) == -1L
		|| fseek(fd, 0, SEEK_SET)) {
		fprintf(stderr, "Error: failed to determine size of input file"
			" (%s)\n", strerror(errno));
		fclose(fd);
		return EXIT_FAILURE;
	}

	insize = (size_t)ret;
	indata = malloc(insize);
	if (!indata) {
		fprintf(stderr, "Error: failed to allocate %u bytes for input"
			" file (%s)\n", (unsigned)insize, strerror(errno));
		fclose(fd);
		return EXIT_FAILURE;
	}

	if (fread(indata, 1, insize, fd) != insize || ferror(fd)) {
		fprintf(stderr, "Error: failed to read input file (%s)\n",
			strerror(errno));
		free(indata);
		fclose(fd);
		return EXIT_FAILURE;
	}

	if (fclose(fd) != 0) {
		fprintf(stderr, "Error: failed to close input file (%s)\n",
			strerror(errno));
		free(indata);
		return EXIT_FAILURE;
	}

	fd = fopen(argv[2], "wb");
	if (!fd) {
		fprintf(stderr, "Error: failed to open output file (%s)\n",
			strerror(errno));
		free(indata);
		return EXIT_FAILURE;
	}

	if (refpack_brute_force_compress(indata, insize, &outdata, &outsize)
		< 0) {
		fprintf(stderr, "Error: refpack_brute_force_compress failed"
			" (%s)\n", strerror(errno));
		free(indata);
		fclose(fd);
		return EXIT_FAILURE;
	}

	free(indata);

	if (fwrite(outdata, 1, outsize, fd) != outsize || ferror(fd)) {
		fprintf(stderr, "Error: failed to write output file (%s)\n",
			strerror(errno));
		free(outdata);
		fclose(fd);
		return EXIT_FAILURE;
	}

	free(outdata);

	if (fclose(fd) != 0) {
		fprintf(stderr, "Error: failed to close output file (%s)\n",
			strerror(errno));
		return EXIT_FAILURE;
	}

	return EXIT_SUCCESS;
}