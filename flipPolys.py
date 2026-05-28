# -*- coding: utf-8 -*-
"""
Implementation of FlipPolys
Version 1.0
Date 2026-05-28

@author: Christopher Wolf, chris/at/Christopher-Wolf.de

The programme is under GNU General Public License v3, but not any later version.
https://www.gnu.org/licenses/gpl-3.0.html
The software is given "as it is", without the assumption that it can be used for a specific purpose.
In particular, it is not a reference implementation for FlipPolys as the source code
certainly contains vulnerabilities against side channel attacks.

Apart from that, it should help to illustrate the concepts of FlipPolys.

Polynomials over GF(2) are respresented as numbers, e.g.
  0 -> 0 = 00000b
  1 -> 1 = 00001b
  X -> 2 = 00010b
  X^2 + X -> 6 = 0110b
  X^4 + X -> 18 = 10010b
"""

import math
import random
import datetime

from flipFields import *


############################################################################
# Computations
# 
def polyMul(a,b,D, relaxed=False):
  """
  Computes a*b in the FlipPolys constructed by D. a, b are interpreted as bit-vectors

  Parameters
  ----------
  a : int
    Polynomial over GF(2), stored in an integer.
  b : int
    Polynomial over GF(2), stored in an integer.
  D :  int
    Constructs the corresponding FlipPolys.
  relaxed : Bool
    Skip asserts in the execution  

  Returns
  -------
  (a*b) mod D
  """
  if not(relaxed):
    assert isElem(a,D), "is not an element a=%d for D=%d"%(a,D)
    assert isElem(b,D), "is not an element b=%d for D=%d"%(b,D)
    log2 = log2int(D)
  else:  
    log2 = max(log2int(D),log2int(a),log2int(b))+1
  res = 0
  for i in range(log2):
    for j in range(log2):
      res ^= (a & (1 << i)) * (b & (1 << j))
  if not(relaxed): 
    res %= D
    assert isElem(res,D), "Wrong output with "+str(res)
  return res
  

def eucQuot(a,b):
  """
  Computes the quotient of the Euclidian divion for a / b
  
  Parameters
  ----------
  a : int
    Element of the FlipPolys.
  b : int
    Element of the FlipPolys.

  Returns
  -------
  t : int
    Element of the FlipPolys. Quotient of a / b
  """
  #assert a > b, "a <= b for a=%d and b=%d"%(a,b)
  q = 0; r = a; 
  bDeg = log2int(b); rDeg = log2int(r) 
  while (rDeg >= bDeg) and (r > 0):
    q ^= 1 << (rDeg-bDeg)
    r ^= b << (rDeg-bDeg)
    rDeg = log2int(r)
  return q
  

def invMul(a,D):
  """
  computes a^(-1) mod D, using the extended Euclidian algorithm

  Parameters
  ----------
  a : int
    Element of the FlipPolys.
  D : int
    Constructs the corresponding FlipPolys.

  Returns
  -------
  t : int
    multiplicative inverse of a

  """
  # https://stackoverflow.com/questions/65450416/euclidean-algorithm-for-polynomials-in-gf28
  # https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor
  assert isElem(a,D), "Not an element with "+str(a)
  r2, r1 = a, D
  s2, s1 = 1, 0
  while r1 != 0:
    q = eucQuot(r2, r1)
    r2, r1 = r1, r2 ^ polyMul(q,r1,D,relaxed=True)
    s2, s1 = s1, s2 ^ polyMul(q,s1,D,relaxed=True)
    mulR = polyMul(q,r1,D,relaxed=True)
    mulS = polyMul(q,s1,D,relaxed=True)

  assert isElem(s2,D), "s2 not an element with "+str(s2)
  return s2


def invHensel(a,D):
  """
  Computes the multiplicative inverse using Hensel's lifting.
  See for details (German):
  https://hwlang.de/zahlentheorie/hensel-lifting.htm  

  Parameters
  ----------
  a : int
    element of the corresponding flipPolys
  D : int
    Modulus of the flipField.

  Returns
  -------
  t : int
    Integer t s/t a.t = 1 (mod D)
  """    
  def invRec(a, k):
     if k == 1: return 1
     D = 2**k
     a = a % D
     r = invRec(a, (k+1)//2)
     tmp = polyMul(a,r,D,relaxed=True)
     res = polyMul(tmp,r,D,relaxed=True)
     return res % D
   
   
  assert isElem(a,D), "is not an element a=%d for D=%d"%(a,D)
  k = log2int(D)
  assert 2**k == D, "k invalid for k=%d, D=%d"%(k,D)
  return invRec(a,k)

############################################################################
# Unit Testing
def testAll():
  """
  Unit Testing for this file

  Returns
  -------
  None.

  """
  print("Start Testing flipPolys")

  if log2int(4) != 2: print("Error log2int.1 with %d"%(log2int(4)))
  if log2int(16) != 4: print("Error log2int.2 with %d"%(log2int(16)))
  if log2int(256) != 8: print("Error log2int.3 with %d"%(log2int(256)))
  if log2int(5) != 2: print("Error log2int.4 with %d"%(log2int(5)))
  if log2int(31) != 4: print("Error log2int.5 with %d"%(log2int(31)))
  if log2int(300) != 8: print("Error log2int.6 with %d"%(log2int(300)))

  res = polyMul(1,3,16)
  if res != 3: print("Error polyMul.1 with %d"%(res))
  res = polyMul(3,3,16)
  if res != 5: print("Error polyMul.2 with %d"%(res))
  res = polyMul(5,5,16)
  if res != 1: print("Error polyMul.3 with %d"%(res))
  res = polyMul(3,15,16)
  if res != 1: print("Error polyMul.4 with %d"%(res))
  res = polyMul(5,15,16)
  if res != 3: print("Error polyMul.5 with %d"%(res))
  res = polyMul(7,11,16)
  if res != 1: print("Error polyMul.6 with %d"%(res))
  res = polyMul(1,16,16,relaxed=True)
  if res != 16: print("Error polyMul.7 with %d"%(res))
  res = polyMul(3,16,16,relaxed=True)
  if res != 48: print("Error polyMul.8 with %d"%(res))
  
  res = eucQuot(2,1)
  if res != 2: print("Error eucQuot.1 with %d"%(res))
  res = eucQuot(16,7)
  if res != 6: print("Error eucQuot.2 with %d"%(res))
  res = eucQuot(32,5)
  if res != 10: print("Error eucQuot.3 with %d"%(res))
  res = eucQuot(27,6)
  if res != 4: print("Error eucQuot.4 with %d"%(res))
  res = eucQuot(27,3)
  if res != 9: print("Error eucQuot.5 with %d"%(res))
  res = eucQuot(27,1)
  if res != 27: print("Error eucQuot.6 with %d"%(res))  

  res = invMul(5,16)
  if res != 5: print("Error invMul.1 with %d"%(res))
  res = invMul(3,16)
  if res != 15: print("Error invMul.2 with %d"%(res))
  res = invMul(15,16)
  if res != 3: print("Error invMul.3 with %d"%(res))
  res = invMul(7,16)
  if res != 11: print("Error invMul.4 with %d"%(res))
  res = invMul(11,16)
  if res != 7: print("Error invMul.5 with %d"%(res))
  res = invMul(11,256)
  res2 = polyMul(11,res,256)
  if res2 != 1: print("Error invMul.6 with %d and %d"%(res,res2))
  res = invMul(17,256)
  res2 = polyMul(17,res,256)
  if res2 != 1: print("Error invMul.7 with %d and %d"%(res,res2))
  res = invMul(17,65536)
  res2 = polyMul(17,res,65536)
  if res2 != 1: print("Error invMul.8 with %d and %d"%(res,res2))
  res = invMul(1,16)
  res2 = polyMul(1,res,16)
  if res2 != 1: print("Error invMul.9 with %d and %d"%(res,res2))
  res = invMul(1,65536)
  res2 = polyMul(1,res,65536)
  if res2 != 1: print("Error invMul.10 with %d and %d"%(res,res2))
  res = invMul(637,65536)
  res2 = polyMul(637,res,65536)
  if res2 != 1: print("Error invMul.11 with %d and %d"%(res,res2))  
  res = invMul(3,65536)
  res2 = polyMul(3,res,65536)
  if res2 != 1: print("Error invMul.12 with %d and %d"%(res,res2))  
  res = invMul(65531,65536)
  res2 = polyMul(65531,res,65536)
  if res2 != 1: print("Error invMul.13 with %d and %d"%(res,res2))
  res = invMul(1023,65536)
  res2 = polyMul(1023,res,65536)
  if res2 != 1: print("Error invMul.14 with %d and %d"%(res,res2))
  a = 1; D = 4; res = invMul(a,D);
  res2 = polyMul(a,res,D)
  if res2 != 1: print("Error invMul.15 with %d and %d"%(res,res2))
  a = 3; D = 4; res = invMul(a,D);
  res2 = polyMul(a,res,D)
  if res2 != 1: print("Error invMul.16 with %d and %d"%(res,res2))
  a = 1; D = 16; res = invMul(a,D); res2 = polyMul(a,res,D)
  if res2 != 1: print("Error invMul.17 with %d and %d"%(res,res2))
  a = 3; D = 16; res = invMul(a,D); res2 = polyMul(a,res,D)
  if res2 != 1: print("Error invMul.18 with %d and %d"%(res,res2))
  a = 15; D = 16; res = invMul(a,D); res2 = polyMul(a,res,D)
  if res2 != 1: print("Error invMul.19 with %d and %d"%(res,res2))
  a = 13; D = 16; res = invMul(a,D); res2 = polyMul(a,res,D)
  if res2 != 1: print("Error invMul.20 with %d and %d"%(res,res2))  

  D = 1024; a = 3
  i = invHensel(a,D); i2 = invMul(a,D)
  if i != i2: print("Error invHensel.1 %d %d"%(i,i2))
  D = 1024; a = 7
  i = invHensel(a,D); i2 = invMul(a,D)
  if i != i2: print("Error invHensel.2 %d %d"%(i,i2))
  D = 2048; a = 1023
  i = invHensel(a,D); i2 = invMul(a,D)
  if i != i2: print("Error invHensel.3 %d %d"%(i,i2))

  print("Done Testing")


#testAll()
#for i in range(1,32,2):
#  print("{:0d} & {:0d}\\\\".format((i-1)//2,(invMul(i ,32)-1)//2))

