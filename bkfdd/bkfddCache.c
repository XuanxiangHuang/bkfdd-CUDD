/**
  @file

  @ingroup bkfdd

  @brief Functions for inner cache lookup.

  @author Xuanxiang Huang

	@copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All functions are originate from cuddCache.c.
	
	@Modification and Extension details
		1. Add special version of cache look up functions.
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

/**
	@brief Special version of Cache lookup, they won't reclaim dead node, since
		they assumes there is no dead nodes. Used in inner boolean operation.
	
	@see cuddCacheLookup cuddCacheLookup1 cuddCacheLookup2

*/
DdNode *
cuddCacheLookup_Inner(
  DdManager * table,
  ptruint op,
  DdNode * f,
  DdNode * g,
  DdNode * h)
{
	int posn;
	DdCache *en,*cache;
	ptruint uf, ug, uh;
	uf = (ptruint) f | (op & 0xe);
	ug = (ptruint) g | (op >> 4);
	uh = (ptruint) h;
	cache = table->cache;
#ifdef DD_DEBUG
	if (cache == NULL) {
		return(NULL);
	}
#endif
	posn = ddCHash2(uh,uf,ug,table->cacheShift);
	en = &cache[posn];
	if (en->data != NULL && en->f==(DdNodePtr)uf && en->g==(DdNodePtr)ug &&
	en->h==uh) {
		table->cacheHits++;
		return(en->data);
	}
	/* Cache miss: decide whether to resize. */
	table->cacheMisses++;
	if (table->cacheSlack >= 0 &&
		table->cacheHits > table->cacheMisses * table->minHit) {
		cuddCacheResize(table);
	}
  return(NULL);
} /* end of cuddCacheLookup_Inner */


DdNode *
cuddCacheLookup1_Inner(
  DdManager * table,
  DD_CTFP1 op,
  DdNode * f)
{
	int posn;
	DdCache *en,*cache;
	cache = table->cache;
#ifdef DD_DEBUG
	if (cache == NULL) {
		return(NULL);
	}
#endif
	posn = ddCHash2(op,f,f,table->cacheShift);
	en = &cache[posn];
	if (en->data != NULL && en->f==f && en->h==(ptruint)op) {
		table->cacheHits++;
		return(en->data);
	}
	/* Cache miss: decide whether to resize. */
	table->cacheMisses++;
	if (table->cacheSlack >= 0 &&
		table->cacheHits > table->cacheMisses * table->minHit) {
		cuddCacheResize(table);
	}
	return(NULL);
} /* end of cuddCacheLookup1_Inner */


DdNode *
cuddCacheLookup2_Inner(
  DdManager * table,
  DD_CTFP op,
  DdNode * f,
  DdNode * g)
{
	int posn;
	DdCache *en,*cache;
	cache = table->cache;
#ifdef DD_DEBUG
	if (cache == NULL) {
		return(NULL);
	}
#endif
	posn = ddCHash2(op,f,g,table->cacheShift);
	en = &cache[posn];
	if (en->data != NULL && en->f==f && en->g==g && en->h==(ptruint)op) {
		table->cacheHits++;
		return(en->data);
	}
	/* Cache miss: decide whether to resize. */
	table->cacheMisses++;

	if (table->cacheSlack >= 0 &&
		table->cacheHits > table->cacheMisses * table->minHit) {
		cuddCacheResize(table);
	}
	return(NULL);
} /* end of cuddCacheLookup2_Inner */
