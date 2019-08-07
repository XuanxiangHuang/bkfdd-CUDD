/**
  @file

  @ingroup bkfdd

  @brief Internal Functions of the BKFDD part.

	@author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All BKFDD's Functions are originated from CUDD's Functions.
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

#ifndef BKFDD_INT_H
#define BKFDD_INT_H

#include "cuddInt.h"

/* bkfdd expansion(decomposition) types */
	// classical expansion
	#define CS			1
	#define CPD			2
	#define CND			3
	// biconditional expansion
	#define BS			4
	#define BPD			5
	#define BND			6
	// max number of davio expansions allowed to exist.
	#define DAVIO_EXIST_BOUND 200

/* bkfdd mode */
	#define MODE_SND 0	// only S and ND are introduced during building.
	#define MODE_SD 1	// all expansions are introduced during building.

/* 
	In BKFDD'theory, the only terminal is logic 0, and low-edge must be regular.
	To compatible with CUDD's implementation, the auxiliary
	function of variable changed from 0 to 1, and terminal from logic 0 to logic 1.

	These changes make strucure of BDD nodes and FDD nodes different from the BKFDD's theory.
	For BDD node, we have (pv, aux_1, 1, 0), i.e. auxiliary function equal to 1,
	and low terminal is 1, high terminal is 0.

	CS: (x equiv. 1)*f_1 + !(x equiv. 1)*f_0
	ND: f_1 xor !(x equiv. 1)*f_2
	PD: f_0 xor (x equiv. 1)*f_2
	where f_2 = f_1 xor f_0.

	BS: (x equiv. y)*f_x=y + !(x equiv. y)*f_x=!y
	BND: f_x=y + !(x equiv. y)*f_xor
	BPD: f_x=!y + (x equiv. y)*f_xor
	where f_xor = f_x=y xor f_x=!y.

	Besides, there is a easy way to transform CUDD's BDD to BKFDD,
	1. group sifting.
	2. linear combine: BDD => BiDD
	3. change expansion type: BiDD => BKFDD 
*/

/* Functions of Kronecker functional decision diagrams(KFDDs).
		based on paper "Ordered Kronecker Function Decision Diagrams--
								A Data Structure for Representation and Manipulation of Boolean Functions"
		author: Rolf Drechsler and Bernd Becker
		The puma(KFDDs package) seems too diffcult to use, it is somewhat out-of-date.
===============================================================================
	Functions of Biconditional binary decision diagrams(BBDDs).
		based on paper "Biconditional Binary Decision Diagrams: 
								A Novel Canonical Logic Representation Form"
		author: Luca Amaru, Pierre-Emmanuel Gaillardon, and Giovanni De Micheli
		BBDD package(EPFL) is not highly optimized, but CUDD is.
		And actually BBDD can be implemented by CUDD's tenique, like symmetric checking,
		group-sifting, linear combination.
===============================================================================
	Functions of Bi-Kronecker functional decision diagrams(BKFDDs).
		based on paper "Bi-Kronecker Functional Decision Diagrams:
								A Novel Canonical Representation of Boolean Functions"
		author: Xuanxiang Huang, Kehang Fang, Liangda Fang, Qingliang Chen, etc.

		email: cshxx@stu2016.edu.jnu.cn
*/

/*
===============================================================================
		NOTE: if pD introduced to BKFDDs, vars[index]->ref is unpredictable, 
		one should use Cudd_Regular(vars[index]->ref) instead. Since
		vars array may contain variables decomposed by pD, and these variables
		are complemented.
===============================================================================
*/

/** 
	@brief Check expansion types

	@detail Check given expansion type, is it classical-expansion,
	biconditional-expansion, shannon-like expansion, or davio-like expansion.
	return 1 if success, otherwise return 0.

*/
inline static int 
isCla(int expn)
{
	if (expn == CS) 	{ return(1); }
	if (expn == CND) { return(1); }
	if (expn == CPD) { return(1); }
	return(0);
}

inline static int
isBi(int expn)
{
	if (expn == BS) 	{ return(1); }
	if (expn == BND) { return(1); }
	if (expn == BPD) { return(1); }
	return(0);
}

inline static int
isShan(int expn)
{
	if (expn == CS)	{ return(1); }
	if (expn == BS)	{ return(1); }
	return(0);
}

inline static int
isNDavio(int expn)
{
	if (expn == CND) { return(1); }
	if (expn == BND)	{ return(1); }
	return(0);
}

inline static int
isPDavio(int expn)
{
	if (expn == CPD) { return(1); }
	if (expn == BPD)	{ return(1); }
	return(0);
}

/** bkfddTable.c */
/* Inner find or add nodes to unique table. */
extern DdNode * cuddUniqueInter_Inner(DdManager *unique, int index, DdNode *T, DdNode *E);

/** bkfddCache.c */
/* Inner Cache lookups used in BKFDD. */
extern DdNode * cuddCacheLookup_Inner(DdManager *table, ptruint op, DdNode *f, DdNode *g, DdNode *h);
extern DdNode * cuddCacheLookup1_Inner(DdManager *table, DdNode * (*)(DdManager *, DdNode *), DdNode *f);
extern DdNode * cuddCacheLookup2_Inner(DdManager *table, DdNode * (*)(DdManager *, DdNode *, DdNode *), DdNode *f, DdNode *g);

/** bkfddIte.c */
/* Boolean operation. */
extern DdNode * Bkfdd_Ite(DdManager * dd, DdNode * f, DdNode * g, DdNode * h);
extern DdNode * Bkfdd_And(DdManager * dd, DdNode * f, DdNode * g);
extern DdNode * Bkfdd_Or(DdManager * dd, DdNode * f, DdNode * g);
extern DdNode * Bkfdd_Xor(DdManager * dd, DdNode * f, DdNode * g);
extern DdNode * BkfddAndRecur(DdManager *manager, DdNode *f, DdNode *g);
extern DdNode * BkfddXorRecur(DdManager *manager, DdNode *f, DdNode *g);
extern DdNode * BkfddIteRecur(DdManager * dd, DdNode * f, DdNode * g, DdNode * h);
/* Inner Boolean operation, used in expansion-types-change procedures. */
extern DdNode * BkfddAndRecur_Inner(DdManager *manager, DdNode *f, DdNode *g);
extern DdNode * BkfddXorRecur_Inner(DdManager *manager, DdNode *f, DdNode *g);
extern DdNode * BkfddIteRecur_Inner(DdManager * dd, DdNode * f, DdNode * g, DdNode * h);

/** bkfddChangeExpn.c */
/* Change expansion types. */
extern int changeExpnBetweenSND(DdManager * dd, int level);
extern int changeExpnBetweenNDPD(DdManager * dd, int level);
extern int changeExpnPDtoS(DdManager * dd, int level);
extern int changeExpnStoPD(DdManager * dd, int level);
extern int changeExpnBetweenBiCla(DdManager * dd,	int level);

/** bkfddVarSwap.c */
/* Swap two adjacent variables with different expansions. */
extern int BkfddSwapInPlace(DdManager *table, int x, int y);

/** bkfddGroup.c */
/* BKFDD group sifting. */
extern int bkfddGroupSifting(DdManager * table, int lower, int upper);

/** bkfddTransform.c */
/* Choose Better expansions type. */
extern int chooseSND2(DdManager * table);
extern int chooseSND4(DdManager * table);
//extern int chooseBetterBiDD(DdManager * table);
extern int chooseSD3(DdManager * table);
extern int chooseSD6(DdManager * table);
extern int chooseSD3_restricted(DdManager * table);
extern int chooseSD6_restricted(DdManager * table);

/** bkfddDump.c*/
/* Dump BKFDD to BLIF file. */
extern int Bkfdd_DumpBlif(DdManager * dd, int n, DdNode ** f, char const * const * inames, char const * const * onames, char * mname, FILE * fp);
extern int Bkfdd_DumpBlifBody(DdManager * dd, int n, DdNode ** f, char const * const * inames, char const * const * onames, FILE * fp);

/** bkfddChainReduction.c */
/* BKFDD chain reduction detection. */
extern int Bkfdd_RC_Detection(DdManager * table, int * detected, int * reduced);

#endif /** BKFDD_INT_H */
