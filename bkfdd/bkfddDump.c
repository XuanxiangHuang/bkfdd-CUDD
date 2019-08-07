/**
  @file

  @ingroup bkfdd

  @brief Functions for export BKFDDs into BLIF file.

  @author Xuanxiang Huang

	@copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All functions are originate from cuddExport.c

	@Modification and Extension details
		1. Extend Bkfdd_DumpBlif and bkfddDoDumpBlif to non-Shannon decomposed nodes.
======================================================================

**********************************************************************
	@copyright@parblock
  Copyright (c) 1995-2015, Regents of the University of Colorado

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

  Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

  Neither the name of the University of Colorado nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE.
  @endparblock
**********************************************************************

*/

#include "util.h"
#include "cuddInt.h"
#include "bkfddInt.h"

static int bkfddDoDumpBlif (DdManager *dd, DdNode *f, FILE *fp, st_table *visited, char const * const *names);

/**
  @brief Writes a blif file representing the argument BKFDDs.

  @details Each %BKFDD is written as a network of multiplexers.
  Bkfdd_DumpBlif does not close the file: This is the caller
  responsibility. Bkfdd_DumpBlif uses a minimal unique subset of the
  hexadecimal address of a node as name for it.  If the argument
  inames is non-null, it is assumed to hold the pointers to the names
  of the inputs. Similarly for onames.

  @return 1 in case of success; 0 otherwise (e.g., out-of-memory, file
  system full, or an %ADD with constants different from 0 and 1).

  @sideeffect None

  @see Cudd_DumpBlif Cudd_DumpBlifBody

*/
int
Bkfdd_DumpBlif(
  DdManager * dd /**< manager */,
  int  n /**< number of output nodes to be dumped */,
  DdNode ** f /**< array of output nodes to be dumped */,
  char const * const * inames /**< array of input names (or NULL) */,
  char const * const * onames /**< array of output names (or NULL) */,
  char * mname /**< model name (or NULL) */,
  FILE * fp /**< pointer to the dump file */)
{
	int		nvars = dd->size;
	int		retval;
	int		i;

	/* Write the header (.model .inputs .outputs). */
	if (mname == NULL) {
		retval = fprintf(fp,".model DD\n.inputs");
	} else {
		retval = fprintf(fp,".model %s\n.inputs",mname);
	}
	if (retval == EOF) {
		return(0);
	}

	/* Write reordered input variables,
		i is level, index of inames is variable index.
		if no variable name provided, use variable index */
	for (i = 0; i < nvars; i++) {
		int idx = dd->invperm[i];
		if (inames == NULL) {
			retval = fprintf(fp," %d", idx);
		} else {
			retval = fprintf(fp," %s", inames[idx]);
		}
		if (retval == EOF) goto failure;
	}

	/* Write the .output line. */
	retval = fprintf(fp,"\n.outputs");
	if (retval == EOF) goto failure;
	for (i = 0; i < n; i++) {
		if (onames == NULL) {
			retval = fprintf(fp," f%d", i);
		} else {
			retval = fprintf(fp," %s", onames[i]);
		}
		if (retval == EOF) goto failure;
	}
	retval = fprintf(fp,"\n");
	if (retval == EOF) goto failure;

	/* Write biconditional line. i is level.
		if varX associated with biconditional expansions, 
		and varY is its auxiliary function,	we have 
		bkf_X_Y = varX \equiv. varY. where X and Y are
		index of variable. */
	for (i = 0; i < nvars; i ++) {
		if (isBi(dd->expansion[i])) {
			/* Get variable index */
			int pv = dd->invperm[i];
			int sv = dd->invperm[i+1];
			if (inames == NULL) {
				retval = fprintf(fp,".names %d %d bkf_%d_%d\n11 1\n00 1\n",
				pv, sv, pv, sv);
			} else {
				retval = fprintf(fp,".names %s %s bkf_%d_%d\n11 1\n00 1\n",
				inames[pv], inames[sv], pv, sv);
			}
			if (retval == EOF) goto failure;
		}
	}

	retval = Bkfdd_DumpBlifBody(dd, n, f, inames, onames, fp);
	if (retval == 0) goto failure;

	/* Write trailer and return. */
	retval = fprintf(fp,".end\n");
	if (retval == EOF) goto failure;

	return(1);

failure:
	return(0);

} /* end of Bkfdd_DumpBlif */


/**
  @brief Writes a blif body representing the argument BKFDDs.

  @details Each %BKFDD is written as a network of multiplexers.  No
  header (.model, .inputs, and .outputs) and footer (.end) are
  produced by this function.  One multiplexer is written for each %BKFDD
  node.  Bkfdd_DumpBlifBody does not close the file: This is the caller
  responsibility. Bkfdd_DumpBlifBody uses a minimal unique subset of
  the hexadecimal address of a node as name for it.  If the argument
  inames is non-null, it is assumed to hold the pointers to the names
  of the inputs. Similarly for onames. This function prints out only
  .names part.

  @return 1 in case of success; 0 otherwise (e.g., out-of-memory, file
  system full, or an %ADD with constants different from 0 and 1).

  @sideeffect None

  @see Cudd_DumpBlif Cudd_DumpBlifBody

*/
int
Bkfdd_DumpBlifBody(
  DdManager * dd /**< manager */,
  int  n /**< number of output nodes to be dumped */,
  DdNode ** f /**< array of output nodes to be dumped */,
  char const * const * inames /**< array of input names (or NULL) */,
  char const * const * onames /**< array of output names (or NULL) */,
  FILE * fp /**< pointer to the dump file */)
{
	st_table	*visited = NULL;
	int		retval;
	int		i;

	/* Initialize symbol table for visited nodes. */
	visited = st_init_table(st_ptrcmp, st_ptrhash);
	if (visited == NULL) goto failure;

	/* Call the function that really gets the job done. */
	for (i = 0; i < n; i++) {
		retval = bkfddDoDumpBlif(dd,Cudd_Regular(f[i]),fp,visited,inames);
		if (retval == 0) goto failure;
	}

	/* To account for the possible complement on the root,
	** we put either a buffer or an inverter at the output of
	** the multiplexer representing the top node.
	*/
	for (i = 0; i < n; i++) {
		if (onames == NULL) {
			retval = fprintf(fp, ".names %" PRIxPTR " f%d\n",
			(ptruint) f[i] / (ptruint) sizeof(DdNode), i);
		} else {
			retval = fprintf(fp, ".names %" PRIxPTR " %s\n",
			(ptruint) f[i] / (ptruint) sizeof(DdNode), onames[i]);
		}
		if (retval == EOF) goto failure;
		if (Cudd_IsComplement(f[i])) {
			retval = fprintf(fp,"0 1\n");
		} else {
			retval = fprintf(fp,"1 1\n");
		}
		if (retval == EOF) goto failure;
	}

	st_free_table(visited);
	return(1);

failure:
	if (visited != NULL) st_free_table(visited);
	return(0);

} /* end of Bkfdd_DumpBlifBody */


/**
  @brief Performs the recursive step of Bkfdd_DumpBlif.

  @details Traverses the %BKFDD f and writes a multiplexer-network
  description to the file pointed by fp in blif format. f is assumed
  to be a regular pointer and bkfddDoDumpBlif guarantees this assumption
  in the recursive calls.

  @sideeffect None

*/
static int
bkfddDoDumpBlif(
  DdManager * dd,
  DdNode * f,
  FILE * fp,
  st_table * visited,
  char const * const * names)
{
	DdNode	*T, *E;
	int		retval;

#ifdef DD_DEBUG
	assert(!Cudd_IsComplement(f));
#endif

	/* If already visited, nothing to do. */
	if (st_is_member(visited, f) == 1)
		return(1);

	/* Check for abnormal condition that should never happen. */
	if (f == NULL)
		return(0);

	/* Mark node as visited. */
	if (st_insert(visited, f, NULL) == ST_OUT_OF_MEM)
		return(0);

	/* Check for special case: If constant node, generate constant 1. */
	if (f == DD_ONE(dd)) {
		retval = fprintf(fp, ".names %" PRIxPTR "\n1\n",(ptruint) f / (ptruint) sizeof(DdNode));
		if (retval == EOF) {
			return(0);
		} else {
			return(1);
		}
	}
	if (cuddIsConstant(f))
		return(0);

	/* Recursive calls. */
	T = cuddT(f);
	retval = bkfddDoDumpBlif(dd,T,fp,visited,names);
	if (retval != 1) return(retval);
	E = Cudd_Regular(cuddE(f));
	retval = bkfddDoDumpBlif(dd,E,fp,visited,names);
	if (retval != 1) return(retval);

	/* Get expansion types, 
		if expansion is biconditional, use bkf_X_Y,
		if expansion is classical, use variable name. */
	int lvl = dd->perm[f->index];
	int expn = dd->expansion[lvl];
	if (isBi(expn)) {
		// biconditional
		int sv = dd->invperm[lvl+1];
		retval = fprintf(fp,".names bkf_%d_%d", f->index, sv);
	} else {
		// classical	
		if (names != NULL) {
			retval = fprintf(fp,".names %s", names[f->index]);
		} else {
#if SIZEOF_VOID_P == 8 && SIZEOF_INT == 4
			retval = fprintf(fp,".names %u", f->index);
#else
			retval = fprintf(fp,".names %hu", f->index);
#endif
		}
	}
	if (retval == EOF)
		return(0);

	/* Write multiplexer taking complement arc into account. */
	if (isShan(expn)) {
		if (Cudd_IsComplement(cuddE(f))) {
			retval = fprintf(fp," %" PRIxPTR " %" PRIxPTR " %" PRIxPTR "\n11- 1\n0-0 1\n",
			(ptruint) T / (ptruint) sizeof(DdNode),
			(ptruint) E / (ptruint) sizeof(DdNode),
			(ptruint) f / (ptruint) sizeof(DdNode));
		} else {
			retval = fprintf(fp," %" PRIxPTR " %" PRIxPTR " %" PRIxPTR "\n11- 1\n0-1 1\n",
			(ptruint) T / (ptruint) sizeof(DdNode),
			(ptruint) E / (ptruint) sizeof(DdNode),
			(ptruint) f / (ptruint) sizeof(DdNode));
		}
	} else if (isNDavio(expn)){
		if (Cudd_IsComplement(cuddE(f))) {
			retval = fprintf(fp," %" PRIxPTR " %" PRIxPTR " %" PRIxPTR "\n11- 1\n-11 1\n000 1\n",
			(ptruint) T / (ptruint) sizeof(DdNode),
			(ptruint) E / (ptruint) sizeof(DdNode),
			(ptruint) f / (ptruint) sizeof(DdNode));
		} else {
			retval = fprintf(fp," %" PRIxPTR " %" PRIxPTR " %" PRIxPTR "\n11- 1\n-10 1\n001 1\n",
			(ptruint) T / (ptruint) sizeof(DdNode),
			(ptruint) E / (ptruint) sizeof(DdNode),
			(ptruint) f / (ptruint) sizeof(DdNode));
		}
	} else { // pDavio
		if (Cudd_IsComplement(cuddE(f))) {
			retval = fprintf(fp," %" PRIxPTR " %" PRIxPTR " %" PRIxPTR "\n01- 1\n-11 1\n100 1\n",
			(ptruint) T / (ptruint) sizeof(DdNode),
			(ptruint) E / (ptruint) sizeof(DdNode),
			(ptruint) f / (ptruint) sizeof(DdNode));
		} else {
			retval = fprintf(fp," %" PRIxPTR " %" PRIxPTR " %" PRIxPTR "\n01- 1\n-10 1\n101 1\n",
			(ptruint) T / (ptruint) sizeof(DdNode),
			(ptruint) E / (ptruint) sizeof(DdNode),
			(ptruint) f / (ptruint) sizeof(DdNode));
		}
	}

	if (retval == EOF) {
		return(0);
	} else {
		return(1);
	}

} /* end of bkfddDoDumpBlif */
