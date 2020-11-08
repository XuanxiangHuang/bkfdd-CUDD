/**
  @file 

  @ingroup bkfdd

  @brief BKFDD Boolean operations and ITE function.

  @author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All functions are originate from cuddBddIte.c.
	
	@Modification and Extension details
		1. Extend AND, XOR, ITE operations to non-Shannon decomposed nodes.
		2. Add special version of AND, XOR, ITE operations.


	2020/5/4: 
		1. modified davio section of BkfddAndRecur and BkfddAndRecur_Inner
			use rhigh = (flow and glow) xor [(flow xor fhigh) and (glow xor ghigh)]
			instead.
		2. modified davio section of BkfddIteRecur and BkfddIteRecur_Inner
			use definition of ITE(f, g, h) := (f * g) xor (!f * h) instead.
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
#include "bkfddInt.h"

/** Copy from cuddBddIte.c */
static int bddVarToCanonicalSimple (DdManager *dd, DdNode **fp, DdNode **gp, DdNode **hp, int *topfp, int *topgp, int *tophp);

/**
  @brief Implements ITE(f,g,h) of BKFDD.

  @return a pointer to the resulting %BKFDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_bddIte

*/
DdNode *
Bkfdd_Ite(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */,
  DdNode * h /**< third operand */)
{
	DdNode *res;
	do {
		dd->reordered = 0;
		res = BkfddIteRecur(dd,f,g,h);
	} while (dd->reordered == 1);
	if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
		dd->timeoutHandler(dd, dd->tohArg);
	}
	return(res);

} /* end of Bkfdd_Ite */


/**
  @brief Computes the conjunction of two BKFDDs f and g.

  @return a pointer to the resulting %BKFDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_bddAnd

*/
DdNode *
Bkfdd_And(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */)
{
	DdNode *res;
	do {
		dd->reordered = 0;
		res = BkfddAndRecur(dd,f,g);
	} while (dd->reordered == 1);
		if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
		dd->timeoutHandler(dd, dd->tohArg);
	}
	return(res);

} /* end of Bkfdd_And */


/**
  @brief Computes the disjunction of two BKFDDs f and g.

  @return a pointer to the resulting %BKFDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_bddOr

*/
DdNode *
Bkfdd_Or(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */)
{
	DdNode *res;
	do {
		dd->reordered = 0;
		res = BkfddAndRecur(dd,Cudd_Not(f),Cudd_Not(g));
	} while (dd->reordered == 1);
	if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
		dd->timeoutHandler(dd, dd->tohArg);
	}
	res = Cudd_NotCond(res,res != NULL);
	return(res);

} /* end of Bkfdd_Or */


/**
  @brief Computes the exclusive OR of two BKFDDs f and g.

  @return a pointer to the resulting %BKFDD if successful; NULL if the
  intermediate result blows up.

  @sideeffect None

  @see Cudd_bddXnor

*/
DdNode *
Bkfdd_Xor(
  DdManager * dd /**< manager */,
  DdNode * f /**< first operand */,
  DdNode * g /**< second operand */)
{
	DdNode *res;
	do {
		dd->reordered = 0;
		res = BkfddXorRecur(dd,f,g);
	} while (dd->reordered == 1);
	if (dd->errorCode == CUDD_TIMEOUT_EXPIRED && dd->timeoutHandler) {
		dd->timeoutHandler(dd, dd->tohArg);
	}
	return(res);

} /* end of Bkfdd_Xor */


/**
  @brief Implements the recursive step of BkfddAnd.

  @details Takes the conjunction of two BKFDDs.

  @return a pointer to the result is successful; NULL otherwise.

  @sideeffect None

  @see cuddBddAndRecur

*/
DdNode *
BkfddAndRecur(
	DdManager * manager,
	DdNode * f,
	DdNode * g)
{
	DdNode *F, *flow, *fhigh, *G, *glow, *ghigh;
	DdNode *one, *zero, *r, *t, *e;
	F = flow = fhigh = G = glow = ghigh = NULL;
	one = zero = r = t = e = NULL;
	int topf, topg;
	unsigned int index;
	int fdec, gdec, dec;

	statLine(manager);
	one = DD_ONE(manager);
	zero = Cudd_Not(one);

	/* Terminal cases. */
	F = Cudd_Regular(f);
	G = Cudd_Regular(g);
	if (F == G) {
		if (f == g) return(f);
		else return(zero);
	}
	if (F == one) {
		if (f == one) return(g);
		else return(f);
	}
	if (G == one) {
		if (g == one) return(f);
		else return(g);
	}

	/* At this point f and g are not constant. */
	if (f > g) { /* Try to increase cache efficiency. */
		DdNode *tmp = f;
		f = g;
		g = tmp;
		F = Cudd_Regular(f);
		G = Cudd_Regular(g);
	}

	/* Check cache. */
	if (F->ref != 1 || G->ref != 1) {
		r = cuddCacheLookup2(manager, Bkfdd_And, f, g);
		if (r != NULL) return(r);
	}
	checkWhetherToGiveUp(manager);
	/* Here we can skip the use of cuddI, because the operands are known
	** to be non-constant.
	*/
	topf = manager->perm[F->index];
	topg = manager->perm[G->index];
	/* get expansion types of f's root and g's root. */
	fdec = manager->expansion[topf];
	gdec = manager->expansion[topg];
	/* Compute cofactors. */
	if (topf <= topg) {
		index = F->index;
		dec = fdec;
		flow = cuddT(F);
		fhigh = cuddE(F);
		/* Move complemented edge. */
		if (Cudd_IsComplement(f)) {
			flow = Cudd_Not(flow);
			if (isShan(dec)) {
				fhigh = Cudd_Not(fhigh);
			}
		}
	} else { // topf > topg
		index = G->index;
		dec = gdec;
		flow = f;
		if (isShan(dec)) {
			fhigh = f;
		} else {
			fhigh = zero;
		}
	}
	if (topg <= topf) {
		glow = cuddT(G);
		ghigh = cuddE(G);
		if (Cudd_IsComplement(g)) {
			glow = Cudd_Not(glow);
			if (isShan(dec)) {
				ghigh = Cudd_Not(ghigh);
			}
		}
	} else { // topf < topg
		glow = g;
		if (isShan(dec)) {
			ghigh = g;
		} else {
			ghigh = zero;
		}
	}
	if (isShan(dec)) {
		t = BkfddAndRecur(manager, flow, glow);
		if (t == NULL) {
			return(NULL);
		}
		cuddRef(t);

		e = BkfddAndRecur(manager, fhigh, ghigh);
		if (e == NULL) {
			Cudd_IterDerefBdd(manager, t);
			return(NULL);
		}
		cuddRef(e);

		if (t == e) {
			r = t;
		} else {
			if (Cudd_IsComplement(t)) {
				r = cuddUniqueInter(manager,(int)index,Cudd_Not(t),Cudd_Not(e));
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
				r = Cudd_Not(r);
			} else {
				r = cuddUniqueInter(manager,(int)index,t,e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
			}
		}
	} else { // Davio expansion using t xor [(flow xor fhigh) and (glow xor ghigh)]
		t = BkfddAndRecur(manager, flow, glow);
		if (t == NULL) {
			return(NULL);
		}
		cuddRef(t);

		DdNode *tmp1 = BkfddXorRecur(manager, flow, fhigh);
		if (tmp1 == NULL) {
			Cudd_IterDerefBdd(manager, t);
			return(NULL);
		}
		cuddRef(tmp1);

		DdNode *tmp2 = BkfddXorRecur(manager, glow, ghigh);
		if (tmp2 == NULL) {
			Cudd_IterDerefBdd(manager, t);
			Cudd_IterDerefBdd(manager, tmp1);
			return(NULL);
		}
		cuddRef(tmp2);

		DdNode *tmp3 = BkfddAndRecur(manager, tmp1, tmp2);
		if (tmp3 == NULL) {
			Cudd_IterDerefBdd(manager, t);
			Cudd_IterDerefBdd(manager, tmp1);
			Cudd_IterDerefBdd(manager, tmp2);
			return(NULL);
		}
		cuddRef(tmp3);

		e = BkfddXorRecur(manager, t, tmp3);
		if (e == NULL) {
			Cudd_IterDerefBdd(manager, t);
			Cudd_IterDerefBdd(manager, tmp1);
			Cudd_IterDerefBdd(manager, tmp2);
			Cudd_IterDerefBdd(manager, tmp3);
			return(NULL);
		}
		cuddRef(e);

		if (e == zero) {
			r = t;
		} else {
			if (Cudd_IsComplement(t)) {
				r = cuddUniqueInter(manager,(int)index,Cudd_Not(t),e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, tmp1);
					Cudd_IterDerefBdd(manager, tmp2);
					Cudd_IterDerefBdd(manager, tmp3);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
				r = Cudd_Not(r);
			} else {
				r = cuddUniqueInter(manager,(int)index,t,e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, tmp1);
					Cudd_IterDerefBdd(manager, tmp2);
					Cudd_IterDerefBdd(manager, tmp3);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
			}
		}
		/* Dissolve intermediate results. */
		Cudd_IterDerefBdd(manager, tmp1);
		Cudd_IterDerefBdd(manager, tmp2);
		Cudd_IterDerefBdd(manager, tmp3);
	}
	cuddDeref(e);
	cuddDeref(t);
	if (F->ref != 1 || G->ref != 1)
		cuddCacheInsert2(manager, Bkfdd_And, f, g, r);
	return(r);

} /* end of BkfddAndRecur */


/**
  @brief Implements the recursive step of BkfddXor.

  @details Takes the exclusive OR of two BKFDDs.

  @return a pointer to the result is successful; NULL otherwise.

  @sideeffect None

  @see cuddBddXorRecur

*/
DdNode *
BkfddXorRecur(
  DdManager * manager,
  DdNode * f,
  DdNode * g)
{
	DdNode *flow, *fhigh, *G, *glow, *ghigh;
	DdNode *one, *zero, *r, *t, *e;
	int topf, topg;
	unsigned int index;
	int fdec, gdec, dec;
	flow = fhigh = G = glow = ghigh = NULL;
	one = zero = r = t = e = NULL;

	statLine(manager);
	one = DD_ONE(manager);
	zero = Cudd_Not(one);

	/* Terminal cases. */
	if (f == g) return(zero);
	if (f == Cudd_Not(g)) return(one);
	if (f > g) { /* Try to increase cache efficiency and simplify tests. */
		DdNode *tmp = f;
		f = g;
		g = tmp;
	}
	if (g == zero) return(f);
	if (g == one) return(Cudd_Not(f));
	if (Cudd_IsComplement(f)) {
		f = Cudd_Not(f);
		g = Cudd_Not(g);
	}
	/* Now the first argument is regular. */
	if (f == one) return(Cudd_Not(g));

	/* At this point f and g are not constant. */

	/* Check cache. */
	r = cuddCacheLookup2(manager, Bkfdd_Xor, f, g);
	if (r != NULL) return(r);

	checkWhetherToGiveUp(manager);

	/* Here we can skip the use of cuddI, because the operands are known
	** to be non-constant.
	*/
	topf = manager->perm[f->index];
	G = Cudd_Regular(g);
	topg = manager->perm[G->index];

	/* get expansion types of f's root and g's root. */
	fdec = manager->expansion[topf];
	gdec = manager->expansion[topg];

	/* Compute cofactors. */
	if (topf <= topg) {
		index = f->index;
		dec = fdec;
		flow = cuddT(f);
		fhigh = cuddE(f);
	} else { // topf > topg
		index = G->index;
		dec = gdec;
		flow = f;
		if (isShan(dec)) {
			fhigh = f;
		} else {
			fhigh = zero;
		}
	}

	if (topg <= topf) {
		glow = cuddT(G);
		ghigh = cuddE(G);
		if (Cudd_IsComplement(g)) {
			glow = Cudd_Not(glow);
			if (isShan(dec)) {
				ghigh = Cudd_Not(ghigh);
			}
		}
	} else {
		glow = g;
		if (isShan(dec)) {
			ghigh = g;
		} else {
			ghigh = zero;
		}
	}

	t = BkfddXorRecur(manager, flow, glow);
	if (t == NULL) {
		return(NULL);
	}
	cuddRef(t);

	e = BkfddXorRecur(manager, fhigh, ghigh);
	if (e == NULL) {
		Cudd_IterDerefBdd(manager, t);
		return(NULL);
	}
	cuddRef(e);

	if (isShan(dec)) {
		if (t == e) {
			r = t;
		} else {
			if (Cudd_IsComplement(t)) {
				r = cuddUniqueInter(manager,(int)index,Cudd_Not(t),Cudd_Not(e));
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
				r = Cudd_Not(r);
			} else {
				r = cuddUniqueInter(manager,(int)index,t,e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
			}
		}
	} else { // Davio
		if (e == zero) {
			r = t;
		} else {
			if (Cudd_IsComplement(t)) {
				r = cuddUniqueInter(manager,(int)index,Cudd_Not(t),e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
				r = Cudd_Not(r);
			} else {
				r = cuddUniqueInter(manager,(int)index,t,e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
			}
		}
	}
	cuddDeref(e);
	cuddDeref(t);
	cuddCacheInsert2(manager, Bkfdd_Xor, f, g, r);
	return(r);

} /* end of BkfddXorRecur */


/**
  @brief Implements the recursive step of BkfddIte.

  @return a pointer to the resulting %BKFDD. NULL if the intermediate
  result blows up or if reordering occurs.

  @sideeffect None

	@see cuddBddIteRecur

*/
DdNode *
BkfddIteRecur(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  DdNode * h)
{
	DdNode	 *one, *zero, *res;
	DdNode	 *r, *F_l, *F_h, *G_l, *G_h, *H, *H_l, *H_h, *t, *e;
	int		 topf, topg, toph, v;
	unsigned int index;
	int		 comple;
	int fdec, gdec, hdec, dec;
	DdNode *g_xor_h;
	F_l = F_h = G_l = G_h = H = H_l = H_h = NULL;
	one = zero = res = r = t = e = g_xor_h = NULL;

	statLine(dd);
	/* Terminal cases. */
	one = DD_ONE(dd);
	zero = Cudd_Not(one);

	/* One variable cases. */
	if (f == one) 	/* ITE(1,G,H) = G */
		return(g);

	if (f == zero) 	/* ITE(0,G,H) = H */
		return(h);

	/* From now on, f is known not to be a constant. */
	if (g == one || f == g) {	/* ITE(F,F,H) = ITE(F,1,H) = F + H */
		if (h == zero) {	/* ITE(F,1,0) = F */
			return(f);
		} else if (h == one) { /* ITE(F,1,1) = 1 */
			return(h);
		} else {
			res = BkfddAndRecur(dd,Cudd_Not(f),Cudd_Not(h));
			return(Cudd_NotCond(res,res != NULL));
		}
	} else if (g == zero || f == Cudd_Not(g)) { /* ITE(F,!F,H) = ITE(F,0,H) = !F * H */
		if (h == one) {		/* ITE(F,0,1) = !F */
			return(Cudd_Not(f));
		} else if (h == zero) {
			return(h);
		} else {
			res = BkfddAndRecur(dd,Cudd_Not(f),h);
			return(res);
		}
	}
	if (h == zero || f == h) {    /* ITE(F,G,F) = ITE(F,G,0) = F * G */
		res = BkfddAndRecur(dd,f,g);
		return(res);
	} else if (h == one || f == Cudd_Not(h)) { /* ITE(F,G,!F) = ITE(F,G,1) = !F + G */
		res = BkfddAndRecur(dd,f,Cudd_Not(g));
		return(Cudd_NotCond(res,res != NULL));
	}

	/* Check remaining one variable case. */
	if (g == h) { 		/* ITE(F,G,G) = G */
		return(g);
	} else if (g == Cudd_Not(h)) { /* ITE(F,G,!G) = F <-> G */
		res = BkfddXorRecur(dd,f,h);
		return(res);
	}

	/* From here, there are no constants. */
	/* Transform (F,G,H) to standard triple, the CUDD's standard triple
		is that the first 2 arguments must be regular. */
	comple = bddVarToCanonicalSimple(dd, &f, &g, &h, &topf, &topg, &toph);

	/* From here, f and g are regular. */
	v = ddMin(topg, toph);
	H = Cudd_Regular(h);
	fdec = dd->expansion[topf];
	if ( (topf < v) &&
		(cuddT(f) == one) &&
		(Cudd_Regular(cuddE(f)) == one) ) {
		if (isShan(fdec)) {
			assert(cuddE(f) == zero);
			r = cuddUniqueInter(dd, (int) f->index, g, h);
			if (r == NULL) { return(NULL); }
		} else { // Davio expansion
			assert(cuddE(f) == one);
			g_xor_h = BkfddXorRecur(dd, g, h);
			if (g_xor_h == NULL) { return(NULL); }
			cuddRef(g_xor_h);
			r = cuddUniqueInter(dd, (int) f->index, g, g_xor_h);
			if (r == NULL) {
				Cudd_IterDerefBdd(dd,g_xor_h);
				return(NULL);
			}
			cuddDeref(g_xor_h);
		}
		return(Cudd_NotCond(r,comple && r != NULL));
	}

	/* Check cache. */
	r = cuddCacheLookup(dd, DD_BKFDD_ITE_TAG, f, g, h);
	if (r != NULL) {
		return(Cudd_NotCond(r,comple));
	}

	checkWhetherToGiveUp(dd);

	gdec = dd->expansion[topg];
	hdec = dd->expansion[toph];

	/* Compute cofactors. */	
	if (topf <= v) {
		index = f->index;
		dec = fdec;
		/* v = top_var(F,G,H), and v = topf */
		v = topf;
		F_l = cuddT(f);
		F_h = cuddE(f);
	} else { // topf > v
		index = dd->invperm[v];
		dec = dd->expansion[v];
		F_l = f;
		if (isShan(dec)) 	{ F_h = f; }
		else 							{ F_h = zero; }
	}
	/* Now, v = top_var(F,G,H). */
	if (topg == v) {
		assert(index == g->index);
		// we know that g is regular
		assert(dec == gdec);
		G_l = cuddT(g);
		G_h = cuddE(g);
	} else { // topg > v
		G_l = g;
		if (isShan(dec)) 	{ G_h = g; }
		else 							{ G_h = zero; }
	}
	if (toph == v) {	// toph == top_var(F,G,H)
		assert(index == H->index);
		assert(dec == hdec);
		H_l = cuddT(H);
		H_h = cuddE(H);
		if (Cudd_IsComplement(h)) {
			H_l = Cudd_Not(H_l);
			if (isShan(dec)) {
				H_h = Cudd_Not(H_h);
			}
		}
	} else { // toph > v
		H_l = h;
		if (isShan(dec)) 	{ H_h = h; }
		else 							{ H_h = zero; }
	}

	/* Recursive step. */
	if (isShan(dec)) {
		/* Cause g is always regular, by CUDD's standard triples,
		t = ITE(F_l,G_l,H_l) is always regular. */
		t = BkfddIteRecur(dd,F_l,G_l,H_l);
		if (t == NULL) {
			return(NULL);
		}
		cuddRef(t);
		
		e = BkfddIteRecur(dd,F_h,G_h,H_h);
		if (e == NULL) {
			Cudd_IterDerefBdd(dd,t);
			return(NULL);
		}
		cuddRef(e);
		if (t == e) {
			r = t;
		} else {
			r = cuddUniqueInter(dd,(int)index,t,e);
			if (r == NULL) {
				Cudd_IterDerefBdd(dd,t);
				Cudd_IterDerefBdd(dd,e);
				return(NULL);
			}
		}
		cuddDeref(t);
		cuddDeref(e);
	} else { // Davio expansion, we use definition of ITE to compute result
		/* ITE(F, G, H) := F * G + !F * H = (F * G) xor (!F * H) */
		DdNode *tmp1 = BkfddAndRecur(dd, f, g);
		if (tmp1 == NULL) {
			return(NULL);
		}
		cuddRef(tmp1);
		DdNode *tmp2 = BkfddAndRecur(dd, Cudd_Not(f), h);
		if (tmp2 == NULL) {
			Cudd_IterDerefBdd(dd,tmp1);
			return(NULL);
		}
		cuddRef(tmp2);
		r = BkfddXorRecur(dd, tmp1, tmp2);
		if (r == NULL) {
			Cudd_IterDerefBdd(dd,tmp1);
			Cudd_IterDerefBdd(dd,tmp2);
			return(NULL);
		}
		Cudd_IterDerefBdd(dd,tmp1);
		Cudd_IterDerefBdd(dd,tmp2);
	}
	cuddCacheInsert(dd, DD_BKFDD_ITE_TAG, f, g, h, r);
	return(Cudd_NotCond(r,comple));

} /* end of BkfddIteRecur */


/**
  @detial Special version of BKFDD's AND operation, use special
	version of uniqueinter and cachelookup. It won't reclaim dead node,
	all unneeded immediate results will only be Deref, not dispose.
	It won't trigger dynamic reordering, garbage collecting, and
	won't increase dead nodes counter.

*/
DdNode *
BkfddAndRecur_Inner(
	DdManager * manager,
	DdNode * f,
	DdNode * g)
{
	DdNode *F, *flow, *fhigh, *G, *glow, *ghigh;
	DdNode *one, *zero, *r, *t, *e;
	F = flow = fhigh = G = glow = ghigh = NULL;
	one = zero = r = t = e = NULL;
	int topf, topg;
	unsigned int index;
	int fdec, gdec, dec;

	statLine(manager);
	one = DD_ONE(manager);
	zero = Cudd_Not(one);

	/* Terminal cases. */
	F = Cudd_Regular(f);
	G = Cudd_Regular(g);
	if (F == G) {
		if (f == g) return(f);
		else return(zero);
	}
	if (F == one) {
		if (f == one) return(g);
		else return(f);
	}
	if (G == one) {
		if (g == one) return(f);
		else return(g);
	}

	/* At this point f and g are not constant. */
	if (f > g) { /* Try to increase cache efficiency. */
		DdNode *tmp = f;
		f = g;
		g = tmp;
		F = Cudd_Regular(f);
		G = Cudd_Regular(g);
	}

	/* Check cache. */
	if (F->ref != 1 || G->ref != 1) {
		r = cuddCacheLookup2_Inner(manager, Bkfdd_And, f, g);
		if (r != NULL) return(r);
	}

	checkWhetherToGiveUp(manager);

	/* Here we can skip the use of cuddI, because the operands are known
	** to be non-constant.
	*/
	topf = manager->perm[F->index];
	topg = manager->perm[G->index];

	/* get expansion types of f's root and g's root. */
	fdec = manager->expansion[topf];
	gdec = manager->expansion[topg];

	/* Compute cofactors. */
	if (topf <= topg) {
		index = F->index;
		dec = fdec;
		flow = cuddT(F);
		fhigh = cuddE(F);
		/* Move complemented edge. */
		if (Cudd_IsComplement(f)) {
			flow = Cudd_Not(flow);
			if (isShan(dec)) {
				fhigh = Cudd_Not(fhigh);
			}
		}
	} else { // topf > topg
		index = G->index;
		dec = gdec;
		flow = f;
		if (isShan(dec)) {
			fhigh = f;
		} else {
			fhigh = zero;
		}
	}

	if (topg <= topf) {
		glow = cuddT(G);
		ghigh = cuddE(G);
		if (Cudd_IsComplement(g)) {
			glow = Cudd_Not(glow);
			if (isShan(dec)) {
				ghigh = Cudd_Not(ghigh);
			}
		}
	} else { // topf < topg
		glow = g;
		if (isShan(dec)) {
			ghigh = g;
		} else {
			ghigh = zero;
		}
	}

	if (isShan(dec)) {
		t = BkfddAndRecur_Inner(manager, flow, glow);
		if (t == NULL) {
			return(NULL);
		}
		cuddRef(t);

		e = BkfddAndRecur_Inner(manager, fhigh, ghigh);
		if (e == NULL) {
			Cudd_IterDerefBdd(manager, t);
			return(NULL);
		}
		cuddRef(e);

		if (t == e) {
			r = t;
		} else {
			if (Cudd_IsComplement(t)) {
				r = cuddUniqueInter_Inner(manager,(int)index,Cudd_Not(t),Cudd_Not(e));
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
				r = Cudd_Not(r);
			} else {
				r = cuddUniqueInter_Inner(manager,(int)index,t,e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
			}
		}
	} else { // Davio expansion using t xor [(flow xor fhigh) and (glow xor ghigh)]
		t = BkfddAndRecur_Inner(manager, flow, glow);
		if (t == NULL) {
			return(NULL);
		}
		cuddRef(t);

		DdNode *tmp1 = BkfddXorRecur_Inner(manager, flow, fhigh);
		if (tmp1 == NULL) {
			Cudd_IterDerefBdd(manager, t);
			return(NULL);
		}
		cuddRef(tmp1);

		DdNode *tmp2 = BkfddXorRecur_Inner(manager, glow, ghigh);
		if (tmp2 == NULL) {
			Cudd_IterDerefBdd(manager, t);
			Cudd_IterDerefBdd(manager, tmp1);
			return(NULL);
		}
		cuddRef(tmp2);

		DdNode *tmp3 = BkfddAndRecur_Inner(manager, tmp1, tmp2);
		if (tmp3 == NULL) {
			Cudd_IterDerefBdd(manager, t);
			Cudd_IterDerefBdd(manager, tmp1);
			Cudd_IterDerefBdd(manager, tmp2);
			return(NULL);
		}
		cuddRef(tmp3);

		e = BkfddXorRecur_Inner(manager, t, tmp3);
		if (tmp3 == NULL) {
			Cudd_IterDerefBdd(manager, t);
			Cudd_IterDerefBdd(manager, tmp1);
			Cudd_IterDerefBdd(manager, tmp2);
			Cudd_IterDerefBdd(manager, tmp3);
			return(NULL);
		}
		cuddRef(e);

		if (e == zero) {
			r = t;
		} else {
			if (Cudd_IsComplement(t)) {
				r = cuddUniqueInter_Inner(manager,(int)index,Cudd_Not(t),e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, tmp1);
					Cudd_IterDerefBdd(manager, tmp2);
					Cudd_IterDerefBdd(manager, tmp3);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
				r = Cudd_Not(r);
			} else {
				r = cuddUniqueInter_Inner(manager,(int)index,t,e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, tmp1);
					Cudd_IterDerefBdd(manager, tmp2);
					Cudd_IterDerefBdd(manager, tmp3);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
			}
		}
		cuddDeref(tmp1);
		cuddDeref(tmp2);
		cuddDeref(tmp3);
	}
	cuddDeref(e);
	cuddDeref(t);
	if (F->ref != 1 || G->ref != 1)
		cuddCacheInsert2(manager, Bkfdd_And, f, g, r);
	return(r);

} /* end of BkfddAndRecur_Inner */


/**
	@brief Special version of BKFDD's XOR operation, use special
	version of uniqueinter and cachelookup. It won't reclaim dead node,
	all unneeded immediate results will only be Deref, not dispose.
	It won't trigger dynamic reordering, garbage collecting, and
	won't increase dead nodes counter.
*/
DdNode *
BkfddXorRecur_Inner(
  DdManager * manager,
  DdNode * f,
  DdNode * g)
{
	DdNode *flow, *fhigh, *G, *glow, *ghigh;
	DdNode *one, *zero, *r, *t, *e;
	int topf, topg;
	unsigned int index;
	int fdec, gdec, dec;
	flow = fhigh = G = glow = ghigh = NULL;
	one = zero = r = t = e = NULL;

	statLine(manager);
	one = DD_ONE(manager);
	zero = Cudd_Not(one);

	/* Terminal cases. */
	if (f == g) return(zero);
	if (f == Cudd_Not(g)) return(one);
	if (f > g) { /* Try to increase cache efficiency and simplify tests. */
		DdNode *tmp = f;
		f = g;
		g = tmp;
	}
	if (g == zero) return(f);
	if (g == one) return(Cudd_Not(f));
	if (Cudd_IsComplement(f)) {
		f = Cudd_Not(f);
		g = Cudd_Not(g);
	}
	/* Now the first argument is regular. */
	if (f == one) return(Cudd_Not(g));

	/* At this point f and g are not constant. */

	/* Check cache. */
	r = cuddCacheLookup2_Inner(manager, Bkfdd_Xor, f, g);
	if (r != NULL) return(r);

	checkWhetherToGiveUp(manager);

	/* Here we can skip the use of cuddI, because the operands are known
	** to be non-constant.
	*/
	topf = manager->perm[f->index];
	G = Cudd_Regular(g);
	topg = manager->perm[G->index];

	/* get expansion types of f's root and g's root. */
	fdec = manager->expansion[topf];
	gdec = manager->expansion[topg];

	/* Compute cofactors. */
	if (topf <= topg) {
		index = f->index;
		dec = fdec;
		flow = cuddT(f);
		fhigh = cuddE(f);
	} else { // topf > topg
		index = G->index;
		dec = gdec;
		flow = f;
		if (isShan(dec)) {
			fhigh = f;
		} else {
			fhigh = zero;
		}
	}

	if (topg <= topf) {
		glow = cuddT(G);
		ghigh = cuddE(G);
		if (Cudd_IsComplement(g)) {
			glow = Cudd_Not(glow);
			if (isShan(dec)) {
				ghigh = Cudd_Not(ghigh);
			}
		}
	} else {
		glow = g;
		if (isShan(dec)) {
			ghigh = g;
		} else {
			ghigh = zero;
		}
	}

	t = BkfddXorRecur_Inner(manager, flow, glow);
	if (t == NULL) {
		return(NULL);
	}
	cuddRef(t);

	e = BkfddXorRecur_Inner(manager, fhigh, ghigh);
	if (e == NULL) {
		Cudd_IterDerefBdd(manager, t);
		return(NULL);
	}
	cuddRef(e);

	if (isShan(dec)) {
		if (t == e) {
			r = t;
		} else {
			if (Cudd_IsComplement(t)) {
				r = cuddUniqueInter_Inner(manager,(int)index,Cudd_Not(t),Cudd_Not(e));
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
				r = Cudd_Not(r);
			} else {
				r = cuddUniqueInter_Inner(manager,(int)index,t,e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
			}
		}
	} else { // Davio
		if (e == zero) {
			r = t;
		} else {
			if (Cudd_IsComplement(t)) {
				r = cuddUniqueInter_Inner(manager,(int)index,Cudd_Not(t),e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
				r = Cudd_Not(r);
			} else {
				r = cuddUniqueInter_Inner(manager,(int)index,t,e);
				if (r == NULL) {
					Cudd_IterDerefBdd(manager, t);
					Cudd_IterDerefBdd(manager, e);
					return(NULL);
				}
			}
		}
	}
	cuddDeref(e);
	cuddDeref(t);
	cuddCacheInsert2(manager, Bkfdd_Xor, f, g, r);
	return(r);

} /* end of BkfddXorRecur_Inner */


/**
	@brief Special version of BKFDD's ITE operation, use special
	version of uniqueinter and cachelookup. It won't reclaim dead node,
	all unneeded immediate results will only be Deref, not dispose.
	It won't trigger dynamic reordering, garbage collecting, and
	won't increase dead nodes counter.
*/
DdNode *
BkfddIteRecur_Inner(
  DdManager * dd,
  DdNode * f,
  DdNode * g,
  DdNode * h)
{
	DdNode	 *one, *zero, *res;
	DdNode	 *r, *F_l, *F_h, *G_l, *G_h, *H, *H_l, *H_h, *t, *e;
	int		 topf, topg, toph, v;
	unsigned int index;
	int		 comple;
	int fdec, gdec, hdec, dec;
	DdNode *g_xor_h;
	F_l = F_h = G_l = G_h = H = H_l = H_h = NULL;
	one = zero = res = r = t = e = g_xor_h = NULL;

	statLine(dd);
	/* Terminal cases. */
	one = DD_ONE(dd);
	zero = Cudd_Not(one);

	/* One variable cases. */
	if (f == one) 	/* ITE(1,G,H) = G */
		return(g);

	if (f == zero) 	/* ITE(0,G,H) = H */
		return(h);

	/* From now on, f is known not to be a constant. */
	if (g == one || f == g) {	/* ITE(F,F,H) = ITE(F,1,H) = F + H */
		if (h == zero) {	/* ITE(F,1,0) = F */
			return(f);
		} else if (h == one) { /* ITE(F,1,1) = 1 */
			return(h);
		} else {
			res = BkfddAndRecur_Inner(dd,Cudd_Not(f),Cudd_Not(h));
			return(Cudd_NotCond(res,res != NULL));
		}
	} else if (g == zero || f == Cudd_Not(g)) { /* ITE(F,!F,H) = ITE(F,0,H) = !F * H */
		if (h == one) {		/* ITE(F,0,1) = !F */
			return(Cudd_Not(f));
		} else if (h == zero) {
			return(h);
		} else {
			res = BkfddAndRecur_Inner(dd,Cudd_Not(f),h);
			return(res);
		}
	}
	if (h == zero || f == h) {    /* ITE(F,G,F) = ITE(F,G,0) = F * G */
		res = BkfddAndRecur_Inner(dd,f,g);
		return(res);
	} else if (h == one || f == Cudd_Not(h)) { /* ITE(F,G,!F) = ITE(F,G,1) = !F + G */
		res = BkfddAndRecur_Inner(dd,f,Cudd_Not(g));
		return(Cudd_NotCond(res,res != NULL));
	}

	/* Check remaining one variable case. */
	if (g == h) { 		/* ITE(F,G,G) = G */
		return(g);
	} else if (g == Cudd_Not(h)) { /* ITE(F,G,!G) = F <-> G */
		res = BkfddXorRecur_Inner(dd,f,h);
		return(res);
	}

	/* From here, there are no constants. */
	/* Transform (F,G,H) to standard triple, the CUDD's standard triple
		is that the first 2 arguments must be regular. */
	comple = bddVarToCanonicalSimple(dd, &f, &g, &h, &topf, &topg, &toph);

	/* From here, f and g are regular. */
	v = ddMin(topg, toph);
	H = Cudd_Regular(h);
	fdec = dd->expansion[topf];

	if ( (topf < v) &&
		(cuddT(f) == one) &&
		(Cudd_Regular(cuddE(f)) == one) ) {
		if (isShan(fdec)) {
			assert(cuddE(f) == zero);
			r = cuddUniqueInter_Inner(dd, (int) f->index, g, h);
			if (r == NULL) { return(NULL); }
		} else { // Davio expansion
			assert(cuddE(f) == one);
			g_xor_h = BkfddXorRecur_Inner(dd, g, h);
			if (g_xor_h == NULL) { return(NULL); }
			cuddRef(g_xor_h);
			r = cuddUniqueInter_Inner(dd, (int) f->index, g, g_xor_h);
			if (r == NULL) {
				Cudd_IterDerefBdd(dd,g_xor_h);
				return(NULL);
			}
			cuddDeref(g_xor_h);
		}
		return(Cudd_NotCond(r,comple && r != NULL));
	}

	/* Check cache. */
	r = cuddCacheLookup_Inner(dd, DD_BKFDD_ITE_TAG, f, g, h);
	if (r != NULL) {
		return(Cudd_NotCond(r,comple));
	}

	checkWhetherToGiveUp(dd);

	gdec = dd->expansion[topg];
	hdec = dd->expansion[toph];

	/* Compute cofactors. */	
	if (topf <= v) {
		index = f->index;
		dec = fdec;
		/* v = top_var(F,G,H), and v = topf */
		v = topf;
		F_l = cuddT(f);
		F_h = cuddE(f);
	} else { // topf > v
		index = dd->invperm[v];
		dec = dd->expansion[v];
		F_l = f;
		if (isShan(dec)) 	{ F_h = f; }
		else 							{ F_h = zero; }
	}
	/* Now, v = top_var(F,G,H). */
	if (topg == v) {
		assert(index == g->index);
		// we know that g is regular
		assert(dec == gdec);
		G_l = cuddT(g);
		G_h = cuddE(g);
	} else { // topg > v
		G_l = g;
		if (isShan(dec)) 	{ G_h = g; }
		else 							{ G_h = zero; }
	}
	if (toph == v) {	// toph == top_var(F,G,H)
		assert(index == H->index);
		assert(dec == hdec);
		H_l = cuddT(H);
		H_h = cuddE(H);
		if (Cudd_IsComplement(h)) {
			H_l = Cudd_Not(H_l);
			if (isShan(dec)) {
				H_h = Cudd_Not(H_h);
			}
		}
	} else { // toph > v
		H_l = h;
		if (isShan(dec)) 	{ H_h = h; }
		else 							{ H_h = zero; }
	}

	/* Recursive step. */
	if (isShan(dec)) {
		/* Cause g is always regular, by CUDD's standard triples,
		t = ITE(F_l,G_l,H_l) is always regular. */
		t = BkfddIteRecur_Inner(dd,F_l,G_l,H_l);
		if (t == NULL) {
			return(NULL);
		}
		cuddRef(t);
		
		e = BkfddIteRecur_Inner(dd,F_h,G_h,H_h);
		if (e == NULL) {
			Cudd_IterDerefBdd(dd,t);
			return(NULL);
		}
		cuddRef(e);
		if (t == e) {
			r = t;
		} else {
			r = cuddUniqueInter_Inner(dd,(int)index,t,e);
			if (r == NULL) {
				Cudd_IterDerefBdd(dd,t);
				Cudd_IterDerefBdd(dd,e);
				return(NULL);
			}
		}
		cuddDeref(t);
		cuddDeref(e);
	} else { // Davio expansion, we use definition of ITE to compute result
		/* ITE(F, G, H) := F * G + !F * H = (F * G) xor (!F * H) */
		DdNode *tmp1 = BkfddAndRecur_Inner(dd, f, g);
		if (tmp1 == NULL) {
			return(NULL);
		}
		cuddRef(tmp1);
		DdNode *tmp2 = BkfddAndRecur_Inner(dd, Cudd_Not(f), h);
		if (tmp2 == NULL) {
			Cudd_IterDerefBdd(dd,tmp1);
			return(NULL);
		}
		cuddRef(tmp2);
		r = BkfddXorRecur_Inner(dd, tmp1, tmp2);
		if (r == NULL) {
			Cudd_IterDerefBdd(dd,tmp1);
			Cudd_IterDerefBdd(dd,tmp2);
			return(NULL);
		}
		cuddDeref(tmp1);
		cuddDeref(tmp2);
	}
	cuddCacheInsert(dd, DD_BKFDD_ITE_TAG, f, g, h, r);
	return(Cudd_NotCond(r,comple));

} /* end of BkfddIteRecur_Inner */


/**
  @brief Picks unique member from equiv expressions.

  @details Makes sure the first two pointers are regular.  This
  mat require the complementation of the result, which is signaled by
  returning 1 instead of 0.  This function is simpler than the general
  case because it assumes that no two arguments are the same or
  complementary, and no argument is constant.

  @sideeffect None

*/
static int
bddVarToCanonicalSimple(
  DdManager * dd,
  DdNode ** fp,
  DdNode ** gp,
  DdNode ** hp,
  int * topfp,
  int * topgp,
  int * tophp)
{
	DdNode	*r, *f, *g, *h;
	int		comple, change;

	f = *fp;
	g = *gp;
	h = *hp;

	change = 0;

	/* adjust pointers so that the first 2 arguments to ITE are regular */
	if (Cudd_IsComplement(f)) {	/* ITE(!F,G,H) = ITE(F,H,G) */
		f = Cudd_Not(f);
		r = g;
		g = h;
		h = r;
		change = 1;
	}
	comple = 0;
	if (Cudd_IsComplement(g)) {	/* ITE(F,!G,H) = !ITE(F,G,!H) */
		g = Cudd_Not(g);
		h = Cudd_Not(h);
		change = 1;
		comple = 1;
	}
	if (change) {
		*fp = f;
		*gp = g;
		*hp = h;
	}

	/* Here we can skip the use of cuddI, because the operands are known
	** to be non-constant.
	*/
	*topfp = dd->perm[f->index];
	*topgp = dd->perm[g->index];
	*tophp = dd->perm[Cudd_Regular(h)->index];

	return(comple);

} /* end of bddVarToCanonicalSimple */
