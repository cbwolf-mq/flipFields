# -*- coding: utf-8 -*-
"""
Implementation of FlipFields
Version 1.15
Date 2026-09-19

@author: Christopher Wolf, chris/at/Christopher-Wolf.de

For more information, see https://eprint.iacr.org/2026/1088


The programme is under GNU General Public License v3, but not any later version.
https://www.gnu.org/licenses/gpl-3.0.html
The software is given "as it is", without the assumption that it can be used for a specific purpose.
In particular, it is not a reference implementation fo as the source code
certainly contains vulnerabilities against side channel attacks.

Apart from that, it should help to illustrate the concepts of FlipFields.

This file implements general methods, the corresponding
FlipInts and FlipPolys care found in the corresponding files.
"""

# external tools
#import itertools
import datetime
import math
import random
import numpy 
import scipy
from dataclasses import dataclass
#import matplotlib.pyplot as plt

#import flipPolys


#########################################################################
# basic functions

def log2int(D):
  """
  Computes a k such that 2^(k+1) > D >= 2^k, i.e. the logarithm to basis 2.

  Parameters
  ----------
  D : int
    Constructs the corresponding FlipPolys.

  Returns
  -------
  int
    k such that D = 2^k
  """
  res = 0
  while (D > 1): 
    D //= 2
    res += 1
  return res 


def isField(D):
  """
  Checks if D is actually constructing a FlipField
  
  Parameters
  ----------
  D : int
    Must be of the form 2^(d+1) for some non-zero integer d.

  Returns
  -------
  bool
    True iff D has the required form.

  """
  if (D < 3): return False
  while (D > 1): 
    if (D % 2) == 1: return False
    D //= 2
  return True


def isElem(a,D):
  """
  checks if a given input a is actually within the given FlipField D=2^(d+1)
  
  Parameters
  ----------
  a : int
    Potential element for the FlipPoly constructed by D.
  D : int
    Integer of the form 2^(d+1) for some non-negative integer d.

  Returns
  -------
  bool
    True iff 0 <= a < D and a odd
  """
  if not(isField(D)): return False
  if a <= 0: return False
  if a >= D: return False
  if (a % 2) != 1: return False
  return True


# verify if the input is a polynomial with elements from the odd ring
def isPoly(p,D):
  """
  Parameters
  ----------
  p : dict
    Polynomial over a flipField.
  D : int
   Integer of the form 2^(d+1) for some non-negative integer d.

  Returns
  -------
  bool
    True iff all coefficients of the polynomial belong to the flipField.
  """
  for k in p.keys():
    if not(isElem(p[k],D)): return False
  return True    


def isPolyRelaxed(p,D):
  """
  Parameters
  ----------
  p : Polynomial / dictionary
    Input polynomial. Must be from FlipInts
  D : Reduction Module
   Integer of the form 2^(d+1) for some non-negative integer d.

  Returns
  -------
  bool
    True iff the polynomial has its coefficients from FlipInts. Allows 0 coefficients.
  """
  for k in p.keys():
    if not(isElem(p[k],D)) and not(p[k] == 0): return False
  return True    


def isMultiPoly(p,maxDeg,N,D):
  """
  Verifies if the input polynomial is actual a multivariate polynomial.
  This means it's a dictionary, e.g. 
  {"#":1, "3": b, "1#2"} for the polynomial a x_1 x_2 + b x_3 +1 
  

  Parameters
  ----------
  p : dict
    Multivariate Polynomial.
  maxDeg : int
      maximal degree for each monomial
  N : int
    maximal number of variables  
  D : int
    Constructs the corresponding FlipPolys.

  Returns
  -------
  True iff the input is a valid multivariate polynomial.
  """
  assert isField(D), "Wrong field size with {}".format(D)
  
  # check the number of terms
  if (len(p) % 2) != 1: return False
  
  # check if all cofficients are actually in the field
  for k in p.keys(): 
    if not(isElem(p[k],D)): return False
         
  # check if all monomials are well-formed
  for mon in p.keys():
    if mon == "#": continue
    txtList = mon.split("#")
    if len(txtList) > maxDeg: return False
    for var in txtList:
      if int(var) >= N: 
        return False
    for i in range(1,len(txtList)):
      if int(txtList[i-1]) > int(txtList[i]): return False
    
  return True


def avgLists(inLists):
  """ 
  Computes the numerical average of the input lists. The lists can have different length.
  
  Parameters
  ----------
  inLists : list
    List of lists of numbers
    
  Returns 
  list 
    One single list that contains the numerical average of all other lists at this position
  """
  resList = []
  maxLen = max([ len(l) for l in inLists ])
  for i in range(maxLen):
    s = 0; numSum = 0
    for j in range(len(inLists)):
      if i < len(inLists[j]): s += inLists[j][i]; numSum += 1
    resList.append(s / numSum)  
  return resList    


############################################################################
## poly transfer functions
def poly2str(p,isPoly=False):
  """
  Parameters
  ----------
  p : Polynomial / dictionary
    Uses a dictionary as a polynomial
  isPoly : bool
   False: the basis structure is a FlipInts
   True: the basis structure is a FlipPolys

  Returns
  -------
  str - polynomial as a string
  
  Outputs a given polynomial as a string, leading term first
  """
  allKeys = []
  # crude way to transfer keys into a sortable list
  # already exclude zero coefficients
  for k in p.keys():
    if p[k] != 0: allKeys.append(k)
  allKeys.sort(reverse=True)  
  minKey = allKeys[len(allKeys)-1]
  resStr = ""
  for k in allKeys:
    coeffStr = "0{:x} ".format(p[k]) if isPoly else str(p[k])
    if k == 0: resStr += coeffStr
    elif (p[k] != 1): resStr += coeffStr
    if k > 1: resStr += "X^{" +str(k) +"}"
    elif k == 1: resStr += "X"
    if k != minKey: resStr += "+"
  return resStr


# express a given polynomial A(X) mod D as a number
# return this number
def poly2num(A,D):
  """
  Express a given polynomial A(X) mod D as a number
  Return this number

  Parameters
  ----------
  A : list
    Polynomial.
  D : int
    Number generating the corresponding FlipField.

  Returns
  -------
  int
    Polynomial as a number.
  """
  assert isPoly(A,D), "A(X) is not an odd polynomial with "+str(A)
  maxDeg = max(A.keys())
  resNum = 0
  mulBase = 1
  for deg in range(0,maxDeg+1):
    if deg in A: resNum += A[deg]*mulBase
    mulBase *= D
  return resNum  


# given a polynomial A(X) mod D as a number
# reconstruct this polynomial
def num2poly(inNum,D):
  """
  Given a polynomial A(X) mod D as a number
  Reconstruct this polynomial.

  Parameters
  ----------
  inNum : int
    Polynomial as an integer.
  D : int
    Number generating a FlipField.

  Returns
  -------
  list
    Polynomial over this FlipField.
  """
  resPoly = {}
  curDeg = 0
  while inNum > 0:
    curCoeff = inNum % D
    if curCoeff > 0:
      assert isElem(curCoeff, D), "not an element "+str(curCoeff)
      resPoly[curDeg] = curCoeff
    curDeg += 1
    inNum //= D
  isPoly(resPoly,D)  
  return resPoly

############################################################################
# Multivariate polynomials
def multiPoly2str(p):
  """
  Creates a string representation of the corresponding multivariate polynomial p.

  Parameters
  ----------
  p : dict
    Multivariate polynomial.

  Returns
  -------
  str.
  """
  mons = list(p.keys())
  mons.sort()
  return "+".join([ str(p[mon])+"*"+mon for mon in mons ])


def multiPoly2strPretty(p):
  """
  Creates a string representation of the corresponding multivariate polynomial p, properly formated for LaTeX output

  Parameters
  ----------
  p : dict
    Multivariate polynomial.

  Returns
  -------
  str.
  """
  def keyFun(mon):
    if mon == "#": return "9"*10 + "--"
    varCnt = mon.count("#") 
    keyStr =  "sortStr: "+"{:>10}--".format(varCnt)
    for curVar in mon.split("#"):
      keyStr += "{:>10}--".format(curVar)
    return keyStr
  
  #### start multiPoly2strPretty  
  assert len(p) > 0, "Too short polynomial for "+str(p)
  
  mons = list(p.keys())
  mons.sort(key=keyFun,reverse=True)
  
  outList = []
  for mon in mons:
    if mon == "#": outList.append(str(p[mon])); continue
    varList = mon.split('#')
    #print(mon + "- "+str(varList) + "  --- "+str(p))
    varList = [ "x_{"+str(v)+"}" for v in varList ] 
    outMon = "".join(varList)
    outList.append(str(p[mon])+outMon if p[mon] > 1 else outMon)
  #print("outList {}".format(outList))
  return '+'.join(outList)


def list2strMulti(inList):
  """
  For a given list, generates the corresponding string
  as a key for a dictionary:
  a x_1 x_2 -> "1#2"
  b x_3 -> "3"
  1 -> "#" 

  Parameters
  ----------
  inList : list
    list of the form [coeff, var1, var2, ...]

  Returns
  -------
  string

  """
  assert len(inList) >= 1, "List too short"
  
  # first case: constant
  if len(inList) == 1: return "#"
  
  # all other cases now
  inList = inList[1:]
  inList.sort()
  
  outStr = ""  
  for i in range(len(inList)):
    outStr += "{}".format(inList[i])
    if i != len(inList)-1: outStr += "#"
  return outStr


def rndPolyMulti(termNum,maxDeg,N,D,hasConst=True):
  """
  Generates a random multivariate polynomial in N variables.
  a x_1 x_2 + b x_3 +1 is encoded as 
  {"#":1, "3": b, "1#2"}.
  
  Output is both a polynomial over FlipInts or FlipPolys.

  Parameters
  ----------
  termNum : int
    number of terms, must be odd.
  maxDeg : int
    maximal degree of the output monomial
  N : int
    Number of variabless
  D : int    
    Constructs the corresponding FlipPolys.
  hasConst : bool
    If True, ensures there is a constant term in the output  

  Returns
  -------
  Multivariate polynomial.

  """
  assert isField(D), "Not a field for {}".format(D)
  assert (termNum % 2) == 1, "Need an odd number of terms"
  
  resDict = {}; selectListCoeff = [ 2*i+1 for i in range(D//2) ]
  if hasConst: resDict[list2strMulti([1])] = random.choice(selectListCoeff)
  while len(resDict) < termNum:
    # choose a coefficient
    tmpList = [ random.choice(selectListCoeff) ]
    # choose a monomial
    repeat = True
    # With probability 1/2, make it higher degree
    while repeat:
      tmpList.append(random.randrange(N))
      repeat = random.randrange(2) == 0
      if len(tmpList) >= maxDeg: repeat = False
    
    resDict[list2strMulti(tmpList)] = tmpList[0]
  assert isMultiPoly(resDict,maxDeg,N,D), "Wrong Output with "+str(resDict)
  assert len(resDict) == termNum, "Wrong number of terms with "+str(termNum)+" and "+str(len(resDict))+" for "+str(resDict)
  return resDict


def applyMultiPoly(p,A,D):
  """
  Applies the list A to the polynomial p and computes the output.

  Parameters
  ----------
  p : dict
    Multivariate polynomial.
  A : list
    values that need to be applied.
  D : int    
    Constructs the corresponding FlipPolys.

  Returns
  -------
  int - Element of FlipField(D)
  """
  assert isField(D), "Not a field"
  assert isMultiPoly(p,100,len(A),D), "Not a valid multiPoly for {}".format(p)
  
  res = 0
  for mon in p.keys():
    tmp = p[mon]
    if mon != "#": 
      varList = mon.split("#")
      for var in varList:
        tmp *= A[int(var)]
      tmp %= D
      assert isElem(tmp, D), "No element for tmp={} D={}".format(tmp,D)
    res += tmp
  res %= D
  assert isElem(res,D), "No Element for res={} D={}".format(res,D)
  return res
   

############################################################################
# Output function
def plotState(prefix,saveState,outStr):
  """
  Parameters
  ----------
  prefix : str
    Prefix for the output file
  saveState : dict
    Internal state of the function.
  outStr : str
    Output for the current state  

  Returns
  -------
  saveState: dict
    Internal state of the function.
  """
  if not("fileOut" in saveState):
    saveState["fileOut"] = 0
    saveState["now"] = datetime.datetime.now()
  resStr = "Start: " + saveState["now"].strftime("%Y-%m-%d %H:%M:%S") + "\n"
  resStr += "Writing Time: " + datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S") + "\n"
  saveState["fileOut"] = (saveState["fileOut"] +1) % 7
  fileName = "outStat/"+prefix + str(saveState["fileOut"]) + ".txt"
  print("file="+fileName)
  with open(fileName, "w") as f:
    f.write(resStr)
    f.write(outStr)
    f.write("\nEnd\n")
    f.close()  
  return saveState


############################################################################
# lfsr_fcl Find the cycle length for a LFSR

def polyFibStep(A,R,D):  
  """
  Parameters
  ----------
  A : Polynomial / Dictionary
    State of the LFSR
  R : Polynomial / Dictionary
    Feedback polynomial of the LFSR. Must be monic
  D : Mudulus
    Must be a power of 2

  Returns
  -------
  resPoly :  Polynomial / Dictionary
    New state of the polynomial, follows A
    
    
  Implements one step of a Fibonacci Linear Feedback Shift Register. 
  """
  assert isField(D), "Error polyFibStep for D with "+str(D)
  assert isPolyRelaxed(R,D), "Error polyFibStep R(X) - no odd poly for "+str(R)
  redDeg = max(R.keys())
  # count the number of non-zero coefficients
  coeffNum = 0
  for k in R.keys():
    if R[k] != 0: coeffNum += 1
  assert (coeffNum % 2)== 0, "Odd number of terms for R(X) for "+str(R)
  assert R[redDeg] == 1, "Error polyFibStep R(X) is not monic "+str(R)
  ADeg = max(A.keys())
  assert (ADeg+1) == redDeg, "Error polyFibStep ADeg, redDeg"
  for i in range(redDeg): # must be a full polynomial
    assert isElem(A[i],D), "A[i] is not an element for i="+str(i)+" / A[i]="+str(A[i])  
  
  ## either use flipInts or flipPolys
  ## sum up the tabs
  #flipInts  
  sumVal = 0
  for k in R.keys():
    if k == redDeg: continue
    sumVal += A[k]*R[k]     # multiply R(x) by the corresponding term of A(x)
  sumVal %= D
  
  # # flipPolys
  # sumVal = 0
  # for k in R.keys():
  #   if (k == redDeg) or (R[k] == 0): continue
  
  #   log2 = log2int(D)
  #   for i in range(log2):
  #     for j in range(log2):
  #       sumVal ^= (A[k] & (1 << i)) * (R[k] & (1 << j))
  #   sumVal %= D
  
  assert isElem(sumVal,D), "Not an element with "+str(sumVal)
    
  # shift A(x) one step to the right
  resPoly = A.copy()
  for k in range(1,redDeg):
    resPoly[k-1] = A[k]
  resPoly[redDeg-1] = sumVal  # set the highest coefficient of the output    
  return resPoly

      
def fibCycleLength(A,R,D,keepCycle=False):
  """
  Parameters
  ----------
  A : Polynomial / Dictionary
    State of the LFRS
  R : Polynomial / Dictionary
    Reduction Polynomial of the LFSR
  D : FieldInts with modulo D
    All numbers are reduced by the integer D
  keepCycle : bool 
    If True, also return the list of all state polynomials in order as a list

  Returns
  -------
  Integer
    Length of the cycle of the combination A,R,D
  """
  assert isPoly(A,D), "A is not a valid polynomial with "+str(A)
  assert isPolyRelaxed(R,D), "R is not a valid polynomial with "+str(R)
  maxDegRed = max(R.keys())
  maxDegState = max(A.keys())
  assert maxDegState < maxDegRed, "State has a too high degree with deg A="+str(maxDegState)+" and deg R="+str(maxDegRed)
  stateDict = {}; stateList = []
  state = A.copy()
  steps = 0
  while True:
    stateNum = poly2num(state,D)
    if keepCycle: stateList.append(state.copy())
    if stateNum in stateDict: break
    stateDict[stateNum] = steps
    steps += 1
    state = polyFibStep(state,R,D)
  cycLen = steps - stateDict[stateNum]    
  if keepCycle: return cycLen, stateList  
  return cycLen


def findCycle(deg,resNum,D): 
  """
  deg:    int
          gives the degree of the reduction polynomial
  resNum: int
          number of elements to return     
  D:      int
          modulus, must be a power of 2
  """
  targetDeg = deg
  targetPoly = {}
  resPolys = []
  resCycles = []
  # initial state of the reduction polynomial
  for i in range(targetDeg):
    targetPoly[i] = 0
  targetPoly[targetDeg] = 1    # must be monic
  # loop over all possibilities
  finishInc = False
  while not(finishInc):
    
    # work with the polynomial R
    statePoly = {}
    for i in range(targetDeg):
      statePoly[i] = 1
    
    # check if the number of tabs is odd, i.e. the number of terms is even
    tabNum = len(list(filter(lambda v: v != 0, targetPoly.values())))
    if (tabNum % 2) == 0:
      fibLen = fibCycleLength(statePoly,targetPoly,D)
      # insert into the list of winners, delete the last if necessary
      resCycles.append(fibLen); resPolys.append(targetPoly.copy())
      # sort from lowest to highest, bubble sort
      curLast = len(resCycles)-1
      reSwap = True
      while (curLast > 0) and reSwap:
        doSwap = False
        if resCycles[curLast-1] < resCycles[curLast]: doSwap = True
        elif (resCycles[curLast-1] == resCycles[curLast]): 
          tabsLeft = sum([1 if resCycles[curLast-1] != 0 else 0])
          tabsRight = sum([1 if resCycles[curLast] != 0 else 0])        
          if tabsLeft > tabsRight: doSwap = True
        if doSwap:
          # swap
          resCycles[curLast-1], resCycles[curLast] = resCycles[curLast], resCycles[curLast-1]
          resPolys[curLast-1], resPolys[curLast] = resPolys[curLast], resPolys[curLast-1]
          curLast -= 1; reSwap = True
        else: reSwap = False  
      # only report the maximum number of results  
      if len(resPolys) > resNum: resCycles.pop(); resPolys.pop()
    
    # increment the reduction polynomnial 
    incStep = True; incPos = 0
    while incStep and not(finishInc):
      incStep = False
      if targetPoly[incPos] == 0: targetPoly[incPos] = 1 
      else: targetPoly[incPos] += 2
      if targetPoly[incPos] >= D: incStep = True; targetPoly[incPos] = 0; incPos += 1; 
      if incPos >= targetDeg: finishInc = True
  return resCycles, resPolys


def plotCycleLength():
  """
  Saves the reduction polynomials for an LFSR to a file

  Returns
  -------
  None.
  """
  resNum = 10
  fileOut = 0
  now = datetime.datetime.now()
  resStr = "Start: " + now.strftime("%Y-%m-%d %H:%M:%S") + "\n"
  print(now.strftime("%Y-%m-%d %H:%M:%S"))
  for maxDeg in range(2,4):
    for D in [4,8,16]:
      resStr += "\n\n\n"
      resStr += "Params deg=%d, D=%d"%(maxDeg,D) + "\n"
      c,p = findCycle(maxDeg,resNum,D)
      resStr += "Time: " + datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S") + "\n"
      for k in range(len(c)):
        resStr += str(maxDeg) + " & " + str(D) + " & " if k==0 else "  &  & "
        resStr +=  str(c[k]) + " & $" + poly2str(p[k]) + "$\\\\\n"
      
      fileOut = (fileOut +1) % 7
      fileName = "outStat/ints" + str(fileOut) + ".txt"
      print("Time: "+datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
      print("Params deg=%d, D=%d, fileOut=%d"%(maxDeg,D,fileOut))
      with open(fileName, "w") as f:
        f.write(resStr)
        f.write("\nEnd\n")
        f.close()
  
  
def plotCycle():
  """
  For a given set of parameters, plots the full cycle for a giving starting polynomial.
  """
  fieldType = "polys"  
  
  saveState = {}; filePrefix = fieldType+"Plot"; outStr = ""
  plotState(filePrefix,saveState,outStr)

  fullMenu = []
# =============================================================================
#   # new poly
#   newItem = {}
#   newItem["targetPolyStr"] = "X^2 + 3"
#   newItem["targetPoly"] = {2:1, 0:3}; newItem["maxDeg"] = 2; newItem["D"] = 4
#   fullMenu.append(newItem)
#   # new poly
#   newItem = {}
#   newItem["targetPolyStr"] = "X^2 + 3"
#   newItem["targetPoly"] = {2:1, 0:3}; newItem["maxDeg"] = 2; newItem["D"] = 8
#   fullMenu.append(newItem)
#   # new poly
#   newItem = {}
#   newItem["targetPolyStr"] = "X^3 + 3"
#   newItem["targetPoly"] = {3:1, 0:3}; newItem["maxDeg"] = 3; newItem["D"] = 4
#   fullMenu.append(newItem)
# =============================================================================
  # newPoly
  newItem = {}
  newItem["targetPolyStr"] = "X^4 + X^2 + X + 3"
  newItem["targetPoly"] = {4:1, 2:1, 1:1, 0:3}; newItem["maxDeg"] = 4; 
  for D in [4,8,16]:
    newItem["D"] = D
    fullMenu.append(newItem.copy())
  # newPoly
  newItem = {}
  newItem["targetPolyStr"] = "X^5 + X^3 + X + 3"
  newItem["targetPoly"] = {5:1, 3:1, 1:1, 0:3}; newItem["maxDeg"] = 5; 
  for D in [4,8,16]:
    newItem["D"] = D
    fullMenu.append(newItem.copy())

  ##########################################
  # Start evaluating
  for curItem in fullMenu:
    maxDeg = curItem["maxDeg"]; targetPolyStr = curItem["targetPolyStr"]
    targetPoly = curItem["targetPoly"]; D = curItem["D"]
    #outStr += "State: " + str(curItem) + "\n"
    statePoly = {i:1 for i in range(maxDeg)} 
    #statePoly = {i:7 for i in range(maxDeg)} 
    
    cycLen, stateList = fibCycleLength(statePoly,targetPoly,D,keepCycle=True)  
    outStr += "% " + targetPolyStr + "  D=" + str(D) + " with cycle Length " + str(cycLen) + " over " + fieldType + "\n"
    for i in range(cycLen):
      outStr += "" + poly2str(stateList[i],isPoly=True) + "\\rightarrow \n"
    outStr += "(" + poly2str(stateList[cycLen],isPoly=True) + ") \n" + "\n\n"
      
    print(outStr)
     
    plotState(filePrefix,saveState,outStr)
    
    
def polyPredict():
   """
   Checks if we can predict the cycle length for certain reduction polynomials
   """
   
   
   outStr = ""
   for d in range(1,4):
     outStr = "D={}   ".format(2**(d+1))
     for N in range (4,21):
       outStr += str(2**(d-1)*2**(N) - d) + " & "
     print(outStr + "\n")
     
   return   

def TriviumTestPoly():
  """
  Looks for the cycle length for a given polynomial. 
  Saves the result to a file.

  Returns
  -------
  None.

  """
  filePrefix = "trivSearchAffine"
  saveState = {}
  outStr = ""
  # plotState(filePrefix,saveState,outStr)  
  # for N in range(5,16,2):   
  #   for D in [128,1024]:
  for N in [19]:  
    for D in [128]:
      outStr += "\n\nN,D=({},{})\n".format(N,D)
      print("N,D=({},{})".format(N,D))
      A = [1] * N
      
      menu = []
      #p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2-1):1, "0":3} ; menu.append(p.copy())
      #p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2+2):1, "0":3} ; menu.append(p.copy())
      #p = {"{}#{}".format(N//2+1,N//2+2):1, "{}".format(N//2+2):1, "0":3} ; menu.append(p.copy())
      #p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2-1):5, "0":7} ; menu.append(p.copy())
      #p = {"{}#{}".format(N-2,N-1):1, "{}".format(N//2-1):3, "0":3} ; menu.append(p.copy())
      #p = {"{}#{}".format(N//2,N//2+1):3, "{}".format(N//2-1):31, "0":7} ; menu.append(p.copy())
      #p = {"{}#{}".format(N//2,N//2+1):31, "{}".format(N//2-1):31, "0":7} ; menu.append(p.copy())
      #p = {"{}#{}".format(N//2,N//2+1):7, "{}".format(N//2-1):31, "0":7} ; menu.append(p.copy())
      #p = {"{}#{}".format(0,1):17, "{}".format(N//2):1, "0":1} ; menu.append(p.copy())
      #p = {"{}#{}".format(0,1):31, "{}".format(N//2):3, "0":3} ; menu.append(p.copy())
      #p = {"{}#{}".format(0,1):5, "{}".format(N//2):5, "0":5} ; menu.append(p.copy())
      #p = {"{}#{}".format(0,1):15, "{}".format(N//2):7, "0":7} ; menu.append(p.copy())
      #p = {"{}#{}".format(0,2):17, "{}".format(N//2):1, "0":1} ; menu.append(p.copy())
      #p = {"{}#{}".format(0,3):31, "{}".format(N//2):3, "0":3} ; menu.append(p.copy())
      #p = {"{}#{}".format(0,4):5, "{}".format(N//2):5, "0":5} ; menu.append(p.copy())
      #p = {"{}#{}".format(1,4):15, "{}".format(N//2):7, "0":7} ; menu.append(p.copy())
      # p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2-1):3, "0":3} ; menu.append(p.copy())
      # p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2-1):3, "0":7} ; menu.append(p.copy())
      # p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2-1):7, "0":7} ; menu.append(p.copy())
      # p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2-1):31, "0":7} ; menu.append(p.copy())
      
      # p = {"{}".format(N-1):1, "{}".format(N//2):3, "#":1} ; menu.append(p.copy())
      # p = {"{}".format(N-1):7, "{}".format(N//2):3, "#":1} ; menu.append(p.copy())
      # p = {"{}".format(N//2):3, "{}".format(N//2-1):7, "#":1} ; menu.append(p.copy())
      # p = {"{}".format(N//2):7, "{}".format(N//2-1):11, "#":5} ; menu.append(p.copy())
      # p = {"{}".format(1):7, "{}".format(2):11, "#":5} ; menu.append(p.copy())
      # p = {"{}".format(2):7, "{}".format(1):11, "#":5} ; menu.append(p.copy())
      # p = {"{}".format(3):3, "{}".format(0):7, "#":11} ; menu.append(p.copy())
      # p = {"{}".format(3):11, "{}".format(0):3, "#":3} ; menu.append(p.copy())
      # p = {"{}".format(3):15, "{}".format(0):7, "#":7} ; menu.append(p.copy())
      
      # # choosen for quadratic
      # p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2-1):3, "0":31} ; menu.append(p.copy())
      # p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2-1):3, "0":7} ; menu.append(p.copy())
      # p = {"{}#{}".format(N//2,N//2+1):17, "{}".format(N//2-1):31, "0":7} ; menu.append(p.copy())
      
      # # choosen for affine
      p = {"{}".format(3):7, "{}".format(0):11, "#":5} ; menu.append(p.copy())
      p = {"{}".format(3):13, "{}".format(0):5, "#":1} ; menu.append(p.copy())
      p = {"{}".format(3):17, "{}".format(0):11, "#":11} ; menu.append(p.copy())
      
      for p in menu: 
        cl = gaCycleLength(A,p,D)
        outStr += multiPoly2strPretty(p) + "\n"
        outStr += "cycle length {:,d} log: {:.3f}\n".format(cl,math.log(cl))
        outStr += "\n"
        plotState(filePrefix,saveState,outStr)  
      
  return


def TriviumTestFlip():
  """
  Checks a FlipPolynomial in Trivium.

  Returns
  -------
  None
  """
  filePrefix = "trivSearchFlip1024"
  saveState = {} ; saveStateCyc = {}
  outStr = ""; outCyc = ""
  
  
  for N in range(5,18):
    for D in [1024]: 
      outStr += "\n\nN,D=({},{})\n".format(N,D)
      outCyc += "% N,D=({},{})\n".format(N,D)
      print("N,D=({},{})".format(N,D))
  
      
      menu = []
      # # choosen for quadratic
      p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2-1):3, "0":31} ; menu.append(p.copy())
      p = {"{}#{}".format(N//2,N//2+1):1, "{}".format(N//2-1):3, "0":7} ; menu.append(p.copy())
      p = {"{}#{}".format(N//2,N//2+1):17, "{}".format(N//2-1):31, "0":7} ; menu.append(p.copy())
      
      # # choosen for affine
      p = {"{}".format(3):7, "{}".format(0):11, "#":5} ; menu.append(p.copy())
      p = {"{}".format(3):13, "{}".format(0):5, "#":1} ; menu.append(p.copy())
      p = {"{}".format(3):17, "{}".format(0):11, "#":11} ; menu.append(p.copy())
      
      for p in menu: 
        outCyc += "% N={} D={}\n".format(N,D)
        outCyc += "% " + multiPoly2strPretty(p) + "\n"
        outCyc += "{} & {} ".format(N,D)
        for tryCnt in range(10):  
          A = [1] * N
          stateDict = {}
          steps = 0
          while True:
            stateStr = str(A)
            if stateStr in stateDict: break
          
            stateDict[stateStr] = steps
            steps += 1
            
            # update the state, shift A(x) one step to the left
            newVal = applyMultiPoly(p,A,D)  
            A.pop(0)
            A.append(newVal)
            # flip x_0 at random
            assert (D == 128) or (D == 1024), "Wrong D with {}".format(D)
            if D == 128: # 1,3,5
              if random.randrange(2) == 1: A[0] ^= (1 << 1)
              if random.randrange(2) == 1: A[0] ^= (1 << 3)
              if random.randrange(2) == 1: A[0] ^= (1 << 5)
            if D == 1024: # 1,4,7
              if random.randrange(2) == 1: A[0] ^= (1 << 1)
              if random.randrange(2) == 1: A[0] ^= (1 << 4)
              if random.randrange(2) == 1: A[0] ^= (1 << 7) 
          cycLen = stateDict[stateStr]      
            
          outStr += "N={} D={}\n".format(N,D)
          outStr += multiPoly2strPretty(p) + "\n"
          outStr += "cycLen {} \n".format(cycLen)
          outStr += "\n"
          plotState(filePrefix,saveState,outStr)  
          
          outCyc += " & {:,d} ".format(cycLen)
          plotState(filePrefix+"allRes",saveStateCyc,outCyc)  
        outCyc += "\\\\ \n"  
        plotState(filePrefix+"allRes",saveStateCyc,outCyc)  
      outCyc += "\n\n\n"  
      plotState(filePrefix+"allRes",saveStateCyc,outCyc)    
          

############################################################################
# Genetic Algorithm
@dataclass
class geneMultiPoly:
  cycLen: int
  terms: int
  poly: dict
  initialState: list
    
  
  def copy(self):
    return geneMultiPoly(self.cycLen,self.terms,self.poly.copy(),self.initialState.copy()) 
  
       
def gaCycleLength(A,p,D,keepCycle=False):
  """
  Computes the cycle length for a given polynoial p, i.e. the corresponding cycle length
  Parameters
  ----------
  A : Polynomial / Dictionary
    State of the LFRS
  R : Polynomial / Dictionary
    Reduction Polynomial of the LFSR
  D : FieldInts with modulo D
    All numbers are reduced by the integer D
  keepCycle : bool
    Keeps and returns a list of all elements in the cycle  

  Returns
  -------
  Integer
    Length of the cycle of the combination A,R,D
  """
  assert isMultiPoly(p,100,len(A),D), "p is not a valid polynomial with "+str(p)
  stateDict = {}; stateList = []
  state = A.copy()
  steps = 0
  while True:
    stateStr = str(state)
    if keepCycle: stateList.append(state.copy())
    if stateStr in stateDict: break
  
    stateDict[stateStr] = steps
    steps += 1
    
    # update the state, shift A(x) one step to the left
    newVal = applyMultiPoly(p,state,D)  
    state.pop(0)
    state.append(newVal)
  cycLen = steps - stateDict[stateStr]    
  if keepCycle: return cycLen, stateList  
  return cycLen  


def gaFit(gene,N,D):
  """
  Computes the fitness for a given multivariate polynomial as cycLen + 1/terms.
  
  Parameters
  ----------
  gene : geneMultiPoly
    Current gene.
  N : ints
    Number of variables
  D : ints
    All numbers in the polynomial are reduced by the integer D
  
  Returns
  -------
  float: fitness for given parameters c, w,state.
  """
  return gene.cycLen + 1/gene.terms
  

def gaSelect(pop,overallFitness,N,D):
  """
  Selects a mate for mutation or crossover, based on fitness.
  The probability to be selected is proportional to cycLen*N + terms for
  each member of the population.

  Parameters
  ----------
  pop : list of geneMultiPoly
    current population of the genetic algorithm.
  overallFitness : int
    sum of the cycle length, plus terms of the population.
  N : int
    number of variables  
  D : ints
    All numbers in the polynomial are reduced by the integer D  

  Returns
  -------
  random polynomial, based on fitness.
  """
  fitVal = random.random()
  fitVal *= overallFitness
  for g in pop:
    gFit = gaFit(g,N,D)
    if fitVal < gFit: return g
    fitVal -= gFit
  assert False, "Did reach end of gaSelect"  


def gaRun():
  """
  Using a genetic algorithm, find a multivariate polynomial
  in a given number of variables with large cycle length.

  Returns
  -------
  None.
  """
  D = 16
  N = 4
  termNum = 3
  maxDeg = 1
  popSize = 100
  generations = 500
  tries = popSize // 2
  topNum = 10; topCnt = 0; topBreak = 5
  lastFitness = -1
  
  filePrefixAll = "gaTmp"
  
  allResStr = ""
  allResState = {}

  fullPopStr = ""
  fullPopState = {}
  
  saveState = {}; filePrefix = filePrefixAll; outStr = ""
  # chooseList = [ 2*i+1 for i in range(D//2) ]
  plotState(filePrefix,saveState,outStr)
  for N in range(4,18):
    maxMonNum = N**maxDeg   # estimation
    for D in [4,8,16]:
      thisNState = {}
      plotState(filePrefix+ "_N{:02d}_D{:02d}__".format(N,D),thisNState,"")
      dList = [ i*2+1 for i in range(D//2) ]
      
      # create the initial population
      pop = []
      for i in range(popSize):
        p = rndPolyMulti(termNum,maxDeg,N,D)
        #A = [ random.choice(chooseList) for y in range(N) ]
        A = [1] * N
        cycLen = gaCycleLength(A,p,D)
        pop.append(geneMultiPoly(cycLen,len(p.keys()),p,A.copy()))
    
      # Loop over the population and try to improve it
      for curGen in range(generations):
        #print("Gen {}".format(curGen))
        newPop = []
        overallFitness = sum([ gaFit(g,N,D) for g in pop ])
        
        for t in range(tries):
          # select operation
          opCode = random.randrange(100)
          
          g1 = gaSelect(pop,overallFitness,N,D)
          c1 = g1.copy()
          if opCode > 8: g2 = gaSelect(pop,overallFitness,N,D); c2 = g1.copy()
          # execute the corresponding operation
          match opCode:
            case 0 | 1 | 2: 
            # Mutation change coefficient
              mon = random.choice(list(c1.poly.keys()))
              c1.poly[mon] = random.choice(dList)
            case 3 | 4 | 5: 
            # Mutation add monomials
              targetNum = len(c1.poly.keys())+2
              if targetNum < maxMonNum:
                #print("Mutation add in with {} and {}".format(targetNum,c1.poly))
                while len(c1.poly.keys()) < targetNum:
                  addMon = rndPolyMulti(1,maxDeg,N,D,hasConst=False)
                  mon = list(addMon.keys())[0]
                  c1.poly[mon] = addMon[mon]
                #print("Mutation remove out")    
            case 6 | 7 | 8:
            # Mutation remove monomials
              #print("Mutation remove in with {}".format(c1.poly))
              if len(c1.poly.keys()) >= 3 : 
                targetNum = len(c1.poly.keys())-2
                while len(c1.poly.keys()) > targetNum:
                  delMon = random.choice(list(c1.poly.keys()))
                  del c1.poly[delMon]
              #print("Mutation remove out")    
            # case 9 | 10:
            # mutate the start state
            #  changeCoeff = random.randrange(len(c1.initialState))
            #  c1.initialState[changeCoeff] = random.choice(chooseList)
            case _:
            # uniform crossover
              for mon in g1.poly.keys():
                toss = random.randrange(2)
                if toss == 0: c1.poly[mon] = g1.poly[mon]
                else: c2.poly[mon] = g1.poly[mon]
              for mon in g2.poly.keys():
                toss = random.randrange(2)
                if toss == 0: c1.poly[mon] = g2.poly[mon]
                else: c2.poly[mon] = g2.poly[mon]
              # for i in range(N):
              #   toss = random.randrange(2)
              #   if toss != 0: c1.initialState[i], c2.initialState[i] = c2.initialState[i], c1.initialState[i]
              # make sure we have the right number of monomials each  
              while (len(c1.poly.keys()) % 2) != 1:
                #print("c1: {}".format(c1.poly))
                toss = random.randrange(2)
                if toss == 0:
                  addMon = rndPolyMulti(1,maxDeg,N,D,hasConst=False)
                  mon = list(addMon.keys())[0]
                  c1.poly[mon] = addMon[mon]  
                else: 
                  delMon = random.choice(list(c1.poly.keys()))
                  del c1.poly[delMon]
                  #print("del1: {}".format(delMon))
              while (len(c2.poly.keys()) % 2) != 1:
                #print("c2: {}".format(c2.poly))
                toss = random.randrange(2)
                if toss == 0:
                  addMon = rndPolyMulti(1,maxDeg,N,D,hasConst=False)
                  mon = list(addMon.keys())[0]
                  c2.poly[mon] = addMon[mon]  
                else: 
                  delMon = random.choice(list(c2.poly.keys()))
                  del c2.poly[delMon]
                  #print("del2: {}".format(delMon))
          #print("after GA with c1={}".format(c1.poly))        
          # append the new elements to our list
          assert isMultiPoly(c1.poly,maxDeg,N,D), "Invalid child for opCode={}, c1={}".format(opCode,c1)
          c1.cycLen = gaCycleLength(c1.initialState,c1.poly,D)
          #print("Have Cycle Len 1")
          newPop.append(c1)
          if opCode > 8:
            #print("Insert with c2={}".format(c2.poly))
            assert isMultiPoly(c2.poly,maxDeg,N,D), "Invalid child for opCode={}, c2={}".format(opCode,c2)
            c2.cycLen = gaCycleLength(c2.initialState,c2.poly,D)
            #print("Have Cycle Len 2")
            newPop.append(c2)
        ##########################    
        # replace the population
        
        # insert the new genes
        # make sure, newcommers have a higher chance than old members
        pop = pop[:popSize] + newPop + pop[popSize:]
        
        #print("Start sorting")
        outStr += "Start sorting\n"
        # use Bucket Sort
        buckets = {}
        for g in pop:
          if not(g.cycLen) in buckets: buckets[g.cycLen] = []
          buckets[g.cycLen].append(g.copy())
        pop = []
        for l in sorted(list(buckets.keys()),reverse=True):
          buckets[l].sort(key=lambda g: "{:05d}".format(len(g.poly)))
          pop += buckets[l]
          
        # remove duplicates
        oldPop = pop
        pop = []
        popDict = { }
        for curPoly in oldPop:
          polyStr = multiPoly2str(curPoly.poly)
          if not polyStr in popDict:
            pop.append(curPoly)
            popDict[polyStr] = 1
        pop = pop[:popSize]
        
        newBestStr = ""
        for i in range(topNum):
          newBestStr += "Best: cycLen={} for #w={}, p={}, s={}\n".format(pop[i].cycLen,len(pop[i].poly),pop[i].poly,pop[i].initialState)
        topCnt = topCnt+1 if round(lastFitness) == round(overallFitness) else 0
        lastFitness = overallFitness
        outStr += "\n\n\n" 
        if topCnt >= topBreak: outStr += "!!!! Finish !!!! topBest\n"
        if curGen+1 == generations: outStr += "!!!! Finish !!!! generations\n"
        outStr += "overall fitness, log2={:,.5f} value: {:,.3f}\n".format(math.log(overallFitness,2),overallFitness)
        outStr += "N={} D={} popSize={} maxDeg={}\n".format(N,D,len(pop),maxDeg)
        outStr += "gen={} topCnt={}\n".format(curGen,topCnt)
        
        outStr += newBestStr
        
        print(outStr)  
        plotState(filePrefix,saveState,outStr)  
        if topCnt >= topBreak: break
    
      # output the result of this   
      resStr = "\n" + "% topCnt {}".format(topCnt) + " overall fitness, log2={:,.5f} value: {:,.3f}\n".format(math.log(overallFitness,2),overallFitness)
      resStr +=  "% final output for gen={} N={} D={} popSize={} maxDeg={}\n".format(curGen,N,D,len(pop),maxDeg)
    
      resStr += "% order N, D, width, cyclen, poly\n"
      for i in range(topNum):
        stateStr = ""
        stateStr = "%3d"%N if i == 0 else " "*3
        stateStr += " & "
        stateStr += "%d"%D if i == 0 else "  "
        stateStr += " & "
        stateStr += "%4d"%len(pop[i].poly)
        stateStr += " & "
        stateStr += "{:>6,}".format(pop[i].cycLen)
        stateStr += " & "
        stateStr += "$" + multiPoly2strPretty(pop[i].poly) + "$ "
        # stateStr += " & "
        # stateStr += str(pop[i].initialState)
        stateStr += "\\\\\n"
        resStr += stateStr
      resStr += "\\hline\n\n"  
    
      allResStr += resStr
      plotState(filePrefixAll + "_AllRes",allResState,allResStr)
      plotState(filePrefixAll+ "_N{:02d}___".format(N),thisNState,resStr)
      plotState(filePrefix,saveState,outStr)  
      
  
      for i in range(len(pop)):
        stateStr = ""
        stateStr = "%3d"%N if i == 0 else " "*3
        stateStr += " & "
        stateStr += "%4d"%len(pop[i].poly)
        stateStr += " & "
        stateStr += "{:>6,}".format(pop[i].cycLen)
        stateStr += " & "
        stateStr += multiPoly2str(pop[i].poly) 
        stateStr += " & "
        stateStr += str(pop[i].initialState)
        stateStr += "\\\\\n"
        fullPopStr += stateStr
      
      plotState(filePrefixAll + "fullPop",fullPopState,fullPopStr)
      
      
      if len(outStr) > 100 * 1024: outStr = ""
  
############################################################################
def testPolyMult(): 
  """
  Multiply out two specific polynomials, write the result to a file.

  Returns
  -------
  None
  """
  prefix = "polyMul"
  saveState = {}
  outStr = ""
  plotState(prefix,saveState,outStr)
  
  for N in range(3,10):
    A = [ a for a in range(N) ]
    B = [ b for b in range(N) ]
    C = {}
  
    for tryA in range(2**N):
      A = [ a for a in range(N) ]
      i = 0
      while i < N:
        if (tryA % 2) != 0: A[i] = -1
        i += 1
      for tryB in range(2**N):
        B = [ b for b in range(N) ]
        j = 0
        while j < N:
          if (tryB % 2) != 0: B[j] = -1
          j += 1
        # multiply
        C = {}
        for i in range(len(A)):
          for j in range(len(B)):
            if i+j not in C: C[i+j] = []
            if (A[i] != -1) and (B[j] != -1):
              C[i+j].append("a{}*b{}".format(i,j))
        # check for problematic items in C
        isSol = False
        if i in C.keys():
          if len(C[i]) != 0: isSol = True
        if isSol:  
          noProblem = True
          for i in C.keys():
            if (len(C[i]) != 0) and ((len(C[i]) % 2) == 0): noProblem = False
        
          outStr += "N={}, tryA={}, tryB={}\n".format(N,tryA,tryB)  
          if noProblem:
            outStr += "\n\nFound it!\n"
            outStr += "A={}, B={}\n".format(A,B)
            outStr += "C={}\n".format(C)
            for i in C.keys():
              if (len(C[i]) % 2) != 0:
                outStr += "  {}: {}\n".format(i,C[i]) 
            
        plotState(prefix,saveState,outStr)    
  return    

############################################################################
# polynomial multiplication
 
def mulPolys():
  """
  Multiply out two specific polynomials and write the result to a file.

  Returns
  -------
  None
  """
  N = 5
  M = 5
  
  prefix = "mulPloly"
  saveState = {}
  outStr = ""
  
  outStr += "\n\nN={}, M={}\n".format(N,M)
  start = {}
  for i in range(N):
    for j in range(M):
      if not (i+j) in start: start[i+j] = "a{}*b{}".format(i,j)
      else: start[i+j] += "+a{}*b{}".format(i,j)
  for k in [l for l in start.keys()]:
    if (start[k].count('+')) % 2 == 0: del start[k]
    else: outStr += str(start[k]) + "\n"
  plotState(prefix,saveState,outStr)  

  # extract the b-variables
  bVars = {}
  for k in start.keys():
    # select highest b
    goodMons = set()
    line = start[k]       
    terms = line.split('+')
    for t in terms:
      mons = t.split('*')
      for m in mons: 
        if m[0] == 'b': goodMons.add(m)
      bVars[k] = goodMons  
    outStr += "vars: " + str(goodMons) + "\n" 
  # sort the b-variables, extract the highest
  sortedB = {}
  for k in bVars.keys():
    cur = list(bVars[k])
    outStr += "cur {}\n".format(cur)
    cur.sort(key = lambda x: int(x[1:]),reverse=True)
    sortedB[k] = cur
    outStr += "{} sorted: {}\n".format(k,cur) 
    
  # build a system of equations, move one term to the lhs  
  # divide by b_i on both sides
  lhs = {}
  rhs = {}
  for k in sortedB.keys():
    bi = sortedB[k][0]
    outStr += "sortedB={}\n".format(k)
    line = start[k]
    # search for the correct b-var
    allTerms = start[k].split('+')
    outStr += "allTerms={}\n".format(allTerms)
    i = 0; foundIt = False
    while i < len(allTerms):
      mons = allTerms[i].split('*')
      for m in mons:
        outStr += "  have -{}- and -{}-\n".format(bi,m)
        if m == bi: 
          foundIt = True; outStr += "    found {}\n".format(bi)
          lhs[k] = "-"+allTerms[i]; allTerms.pop(i) 
        else: i += 1
        
    outStr += "-{}-".format(bi)  
    outStr += "foundIt={} for {}\n".format(foundIt,k)  
    rhs[k] = "+".join(allTerms)
    outStr += "allTerms={}\n".format(allTerms)
    outStr += "before {}={}\n".format(lhs[k],rhs[k])
    plotState(prefix,saveState,outStr)      
    
  # now, divide by -ai on both sides  
  outStr += "\n\n============================================================\n"  
  for k in sortedB:
    outStr += "lhs=rhs: {} = {}   with {}\n".format(lhs[k],rhs[k],k)
  plotState(prefix,saveState,outStr)      
  outStr += "\n\n"  
  # divide by b_i on both sides  
  for k in sortedB.keys():
    # divide the lhs
    bi = sortedB[k][0]
    allTerms = lhs[k].split('+')
    assert len(allTerms) == 1, "allTerms is {}".format(allTerms)
    # search for the correct b-var
    assert rhs[k].count('+') == 0, "Wrong number of terms for {}".format(start[k])
    print("bi " + bi + " for " + str(k) + "\n")
    outMons = []
    for m in allTerms: 
      for t in m.split('*'):
        if t != bi: outMons.append(t)
    assert len(outMons) == 1, "Too many outMons with {} and {} / {}".format(outMons,bi,k)
    lhs[k] = outMons[0]
    
    # multiply the rhs
    allTerms = rhs[k].split('+')
    outTerms = []
    for t in allTerms: 
      t += "*" + bi + "^{-1}"
      outTerms.append(t)
    rhs[k] = '+'.join(outTerms)  
    outStr += "div b_i / {}={}\n".format(lhs[k],rhs[k]) 
  plotState(prefix,saveState,outStr)  
  
  
def plotGens():
  """  
  Plot Generators for FlipFields.
  """
  
  def isGen(a,D):
    """
    Is "a" a generator for the FlipField of order D//2?

    Parameters
    ----------
    a : int
      element of the FlipField.
    D : int
      FlipField mod D.

    Returns
    -------
    True iff a is a generator.
    """
    resSet = set([ ((a**i) % D) for i in range(D // 2) ])
    #print([ ((a**i) % D) for i in range(D // 2) ], resSet)
    return  resSet == (D // 2)
    
  prefix = "gen"; saveState = {}; outStr = ""
  plotState(prefix,saveState,outStr) 
  for d in [4,8,12,16]:
  #for d in [4]:
    D = 2**d * 2
    numGen = 0
    for a in range(1,D,2):
      #print(a)
      if isGen(a,D): outStr += "{} \n".format(a); numGen += 1
    outStr += "d={}, D={} --- numGen={}\n\n".format(d,D,numGen)
    plotState(prefix,saveState,outStr) 

#########################################################################
# genetic algorithm for statistical purposes

def statGAsplitWM(wm):
  """
  Splits a working mode (wm) string into its parts.
  Returns them as a dictionary.
  
  Example strings: 
    Db,3 - double binomial statistics, s=3
    b,5 - Binomial statistits, s=5

  Parameters
  ----------
  wm : str
    Working mode string.

  Returns
  -------
  dict
    working mode dictionary.
  """
  wmDict = {}
  for s in wm.split(","):
    if s in ["Db","Dp","Sb","Sp","b","p"]: wmDict["stat"] = s; continue
    if s.isdigit(): wmDict["data"] = int(s); continue
    assert False, "Wrong format for working mode with +++{}+++".format(wm)
  return wmDict  


def statGiveData(wm):
  """
  Returns the data for the given statistical experiment.
  Data is aggregated via the function printNumVecResponsive().

  Parameters
  ----------
  wm : dict
    Working mode

  Returns
  -------
  data : list
    list of list of list. Data as list of integers.
  label : list
    Corresponding label, e.g. "n=5, d=2".
  """
  outNum = wm["data"]
  data = []; label = []
  match outNum:
    case 3:
      # Stat n=3 d=2 with rep=99999 and sum=12783
      label.append("s=3, d=2")
      data.append([0, 3, 12, 27, 52, 52, 100, 141, 224, 251, 321, 354, 393, 367, 352, 299, 312, 264, 350, 365, 491, 619, 706, 787, 841, 872, 843, 790, 647, 540, 443, 335, 230, 151, 103, 59, 50, 20, 6, 3, 4, 3, 0, 1])
      # Stat n=3 d=3 with rep=99999 and sum=13582
      label.append("s=3, d=3")
      data.append([5, 26, 81, 104, 127, 202, 169, 223, 254, 303, 347, 375, 418, 377, 407, 357, 328, 290, 350, 410, 446, 611, 711, 789, 816, 827, 880, 749, 610, 538, 437, 366, 225, 145, 102, 79, 47, 22, 15, 10, 1, 3])
      # Stat n=3 d=7 with rep=99999 and sum=13686
      label.append("s=3, d=7")
      data.append([43, 53, 100, 128, 140, 174, 181, 230, 241, 314, 324, 409, 404, 385, 329, 294, 313, 317, 335, 438, 478, 588, 714, 766, 880, 825, 899, 774, 645, 559, 438, 340, 215, 158, 111, 62, 35, 26, 10, 7, 3, 1])
      # Stat n=3 d=10 with rep=99999 and sum=13621
      label.append("s=3, d=10")
      data.append([33, 52, 86, 127, 136, 159, 193, 225, 261, 295, 322, 351, 404, 379, 359, 341, 312, 301, 331, 405, 479, 631, 639, 756, 861, 902, 870, 774, 664, 564, 412, 346, 214, 155, 118, 78, 37, 24, 5, 6, 7, 6, 1])
      # Stat n=3 d=128 with rep=99999 and sum=13528
      label.append("s=3, d=128")
      data.append([31, 68, 105, 123, 153, 155, 202, 244, 262, 298, 335, 348, 411, 351, 302, 323, 307, 315, 295, 373, 533, 624, 671, 740, 899, 841, 863, 750, 709, 556, 430, 311, 225, 143, 92, 62, 33, 14, 17, 6, 7, 1])
      # Stat n=3 d=256 with rep=99999 and sum=13594
      label.append("s=3, d=256")
      data.append([26, 55, 75, 113, 165, 184, 205, 239, 266, 292, 342, 361, 404, 368, 339, 324, 268, 329, 346, 436, 519, 627, 706, 824, 780, 884, 778, 765, 646, 562, 405, 320, 212, 180, 114, 57, 31, 25, 12, 7, 3])
      # Stat n=3 d=384 with rep=99999 and sum=13527
      label.append("s=3, d=384")
      data.append([23, 68, 63, 98, 161, 173, 186, 226, 265, 292, 337, 383, 376, 368, 409, 305, 294, 302, 304, 436, 482, 611, 733, 795, 847, 877, 800, 732, 676, 546, 358, 327, 242, 161, 110, 60, 50, 25, 11, 8, 4, 2, 1])
      # Stat n=3 d=512 with rep=99999 and sum=13636
      label.append("s=3, d=512")
      data.append([27, 53, 68, 139, 149, 167, 201, 191, 240, 333, 298, 372, 414, 389, 336, 346, 310, 300, 315, 379, 523, 635, 742, 792, 878, 815, 818, 786, 659, 524, 457, 329, 206, 188, 80, 64, 49, 23, 20, 13, 4, 2, 2])

    case 5: 
      #Stat n=5 d=2 with rep=99999 and sum=2785
      label.append("n=5, d=2")
      data.append([85, 150, 277, 307, 374, 379, 360, 280, 212, 161, 105, 46, 29, 12, 4, 3, 0, 0, 0, 0, 1])
      #Stat n=5 d=3 with rep=99999 and sum=2862
      label.append("n=5, d=3")
      data.append([120, 207, 272, 314, 370, 393, 365, 301, 201, 151, 83, 39, 20, 12, 6, 4, 3, 0, 1])
      # Stat n=5 d=7 with rep=99999 and sum=2820
      label.append("n=5, d=7")
      data.append([103, 192, 275, 316, 375, 378, 320, 311, 240, 147, 92, 42, 20, 6, 3])
      #Stat n=5 d=10 with rep=99999 and sum=2860
      label.append("n=5, d=10")
      data.append([129, 195, 282, 341, 372, 378, 317, 289, 222, 152, 84, 44, 32, 12, 8, 3])
      #Stat n=5 d=128 with rep=99999 and sum=2904
      label.append("n=5, d=128")
      data.append([81, 198, 264, 329, 381, 404, 346, 331, 228, 151, 98, 43, 31, 13, 5, 0, 0, 1])
      #Stat n=5 d=256 with rep=99999 and sum=2871
      label.append("n=5, d=256")
      data.append([97, 204, 273, 312, 366, 365, 346, 276, 259, 172, 92, 54, 38, 9, 6, 2])
      #Stat n=5 d=384 with rep=99999 and sum=2794
      label.append("n=5, d=384")
      data.append([119, 179, 273, 333, 346, 369, 350, 305, 213, 142, 70, 49, 35, 9, 1, 0, 1])
      #Stat n=5 d=512 with rep=99999 and sum=2972
      label.append("n=5, d=512")
      data.append([112, 187, 284, 324, 397, 394, 372, 306, 238, 156, 100, 57, 28, 11, 3, 2, 1])
      
    case 7: 
      #Stat n=7 d=2 with rep=99999 and sum=686
      label.append("n=7, d=2")
      data.append([190, 239, 149, 80, 22, 5, 1])
      #Stat n=7 d=3 with rep=99999 and sum=689
      label.append("n=7, d=3")
      data.append([238, 234, 124, 62, 25, 5, 1])
      #Stat n=7 d=7 with rep=99999 and sum=670
      label.append("n=7, d=7")
      data.append([198, 235, 149, 66, 14, 5, 1, 2])
      #Stat n=7 d=10 with rep=99999 and sum=690
      label.append("n=7, d=10")
      data.append([253, 194, 135, 69, 23, 12, 1, 2, 1])
      #Stat n=7 d=128 with rep=99999 and sum=675
      label.append("n=7, d=128")
      data.append([211, 228, 135, 69, 24, 7, 1])
      #Stat n=7 d=256 with rep=99999 and sum=685
      label.append("n=7, d=256")
      data.append([222, 214, 130, 76, 28, 14, 1])
      #Stat n=7 d=384 with rep=99999 and sum=741
      label.append("n=7, d=384")
      data.append([246, 245, 152, 58, 29, 8, 3])
      #Stat n=7 d=512 with rep=99999 and sum=734
      label.append("n=7, d=512")
      data.append([215, 249, 153, 77, 34, 1, 4, 1])
      
    case _: assert False, "Wrong working mode with "+str(wm)
  return data, label  
# end statGiveData  


def statGAfitness(wm,training,gene,point=None):
  """
  Computes the fitness as difference between the expected and the predicted values via a quadratic norm.
  The result is a positive integer. The smaller the integer, the better the fit, the better the fitness.

  Parameters
  ----------
  wm : dict
    Working mode.
  training : list
    Empirical results, to be fit via the information from the gene.
  gene : dict
    Data that is needed for the fitting algorithm.
  point : int, default None
    returns a single point instead of the full fitness. 

  Returns
  -------
  int
    Non-negative integer. 0 is a perfect fit, all positiv number give a less and less good fit.
  """
  stat = wm["stat"]
  match stat:
    case "Db": 
      prediction = ( 
        gene["stretchOne"] * scipy.stats.binom.pmf(numpy.arange(len(training)), gene["nGuessOne"], gene["pGuessOne"], gene["locOne"]) 
        + gene["stretchTwo"] * scipy.stats.binom.pmf(numpy.arange(len(training)), gene["nGuessTwo"], gene["pGuessTwo"], gene["locTwo"]) 
      )  
    
    case "Sb": 
      gene["split"] = round(gene["split"])
      if gene["split"] < 0: gene["split"] = 0
      s = gene["split"]
      firstTraining = training[:s]
      secondTraining = training[s:]
      firstPrediction = gene["stretchOne"] * scipy.stats.binom.pmf(numpy.arange(len(firstTraining)), gene["nGuessOne"], gene["pGuessOne"], gene["locOne"]) 
      secondPrediction = gene["stretchTwo"] * scipy.stats.binom.pmf(numpy.arange(len(secondTraining)), gene["nGuessTwo"], gene["pGuessTwo"], gene["locTwo"]) 
      prediction = list(firstPrediction) + list(secondPrediction)
        
    case "Dp": 
      prediction = (gene["stretchOne"] * scipy.stats.poisson.pmf(numpy.arange(len(training)), gene["muOne"],gene["locOne"])
                    + 
                    gene["stretchTwo"] * scipy.stats.poisson.pmf(numpy.arange(len(training)), gene["muTwo"],gene["locTwo"]))
    
    case "Sp": 
      s = int(gene["split"])
      assert s >= 0, "Wrong split with {}".format(s)
      firstTraining = training[:s]
      secondTraining = training[s:]
      firstPrediction = gene["stretchOne"] * scipy.stats.poisson.pmf(numpy.arange(len(firstTraining)), gene["muOne"],gene["locOne"])
      secondPrediction = gene["stretchTwo"] * scipy.stats.poisson.pmf(numpy.arange(len(secondTraining)), gene["muTwo"],gene["locTwo"])
      prediction = list(firstPrediction) + list(secondPrediction)
      
    case "b":       
      prediction = gene["stretch"] * scipy.stats.binom.pmf(numpy.arange(len(training)), gene["nGuess"], gene["pGuess"], gene["loc"])
      
    case "p":
      prediction = gene["stretch"] * scipy.stats.poisson.pmf(numpy.arange(len(training)), gene["mu"],gene["loc"])
      
    case _: assert False, "Unknown wm with "+str(wm)  
    
  if point == None: 
    chiSquare = sum([ (training[i]-prediction[i])**2/abs(prediction[i] if prediction[i] != 0 else 1) for i in range(len(prediction)) ])    
    return float(chiSquare)  
  return prediction[point] if point < len(prediction) else 0


def statGAgiveInitialGene(wm):
  """
  Returns initial settings for the different fittings. These values have been created manually.

  Parameters
  ----------
  wm : dict
    Working mode.

  Returns
  -------
  (dict,dict)
    Gene with the corresponding parameters set, except fitness.
    Rounding instructions
  """
  done = False
  resDict = {}; roundDict = {}
  resDict["fitness"] = -1
          
  if wm["stat"] == "b":  
    roundDict["pGuess"] = 0.0001
    roundDict["stretch"] = 1
    roundDict["loc"] = 0.1
    roundDict["nGuess"] = 0.1
    # binomial distribution
    match wm["data"]:
      case 5: 
        done = True
        resDict = {'pGuess': 0.5473, 'stretch': 3356, 'loc': -7, 'nGuess': 23.0, 'fitness': 961.5805685969608}
        
      case 7:
        done = True
        resDict = {'pGuess': 0.5000, 'stretch': 2200, 'loc': -7, 'nGuess': 23.0, 'fitness': 5930}
  # end wm[stat] = b
  
  if wm["stat"] == "p":
    # poisson distribution
    roundDict["stretch"] = 1
    roundDict["mu"] = 0.01   
    roundDict["loc"] = 0.1

    match wm["data"]:
      case 5: 
        done = True   
        resDict = {'stretch': 2940, 'mu': 9.0, 'loc': -4, 'fitness': 33.188104337711664}       
      case 7: 
        done = True   
        resDict = {'stretch': 2488, 'mu': 7.100000000000001, 'loc': -9, 'fitness': 41.45823453369279}
  # end wm[stat] = p


  if wm["stat"] == "Db":  
    # double binomial distribution
    roundDict["pGuessOne"] = 0.0001
    roundDict["stretchOne"] = 1
    roundDict["locOne"] = 0.01
    roundDict["nGuessOne"] = 0.1
    roundDict["pGuessTwo"] = 0.0001
    roundDict["stretchTwo"] = 1
    roundDict["locTwo"] = 0.01
    roundDict["nGuessTwo"] = 0.1
    match wm["data"]:
      case 3: 
        done = True
        resDict = {'pGuessOne': 0.6801, 'stretchOne': 7000, 'locOne': 0.0, 'nGuessOne': 37.0, 
                   'pGuessTwo': 0.2332, 'stretchTwo': 3000, 'locTwo': 0.0, 'nGuessTwo': 50.0, 
                   'fitness': 58982.84671130601}
        
  
  if wm["stat"] == "Sb":  
    # double binomial distribution
    roundDict["split"] = 1
    roundDict["pGuessOne"] = 0.0001
    roundDict["stretchOne"] = 1
    roundDict["locOne"] = 0.01
    roundDict["nGuessOne"] = 0.1
    roundDict["pGuessTwo"] = 0.0001
    roundDict["stretchTwo"] = 1
    roundDict["locTwo"] = 0.01
    roundDict["nGuessTwo"] = 0.1
    match wm["data"]:
      case 3: 
        done = True
        resDict = {'split': 17, 
                   'pGuessOne': 0.5000, 'stretchOne': 3000, 'locOne': -10, 'nGuessOne': 40.0, 
                   'pGuessTwo': 0.3000, 'stretchTwo': 6000, 'locTwo': -4.0, 'nGuessTwo': 40.0, 
                   'fitness': -1}

  
  if wm["stat"] == "Dp":
    # poisson distribution
    resDict["fitness"] = -1
    
    roundDict["weight"] = 0.0001
    roundDict["stretchOne"] = 1
    roundDict["muOne"] = 0.01   
    roundDict["locOne"] = 0.1
    roundDict["stretchTwo"] = 1
    roundDict["muTwo"] = 0.01   
    roundDict["locTwo"] = 0.1

    match wm["data"]:
      case 3: 
        done = True   
        resDict = {'stretchOne': 2400, 'muOne': 5.09, 'locOne': 5, 
                 'stretchTwo': 9100, 'muTwo': 17.36, 'locTwo': 7, 'fitness': 40850.64829886549}

  
  if wm["stat"] == "Sp":
    # poisson distribution, split into two parts
    resDict["fitness"] = -1
    
    roundDict["split"] = 1
    roundDict["stretchOne"] = 1
    roundDict["muOne"] = 0.01   
    roundDict["locOne"] = 0.1
    roundDict["stretchTwo"] = 1
    roundDict["muTwo"] = 0.01   
    roundDict["locTwo"] = 0.1
  
    match wm["data"]:
      case 3:
        done = True
        resDict = {'split': 17, 'stretchOne': 3300, 'muOne': 13, 'locOne': -1.0, 
                                'stretchTwo': 5000, 'muTwo': 7, 'locTwo': 0, 'fitness': -1,}
  # end stat==Sp      
          
  assert done, "Wrong working mode with "+str(wm) 
  return resDict, roundDict


def statGAroundGene(roundDict,gene):
  """
  Rounds all values in the current gene according to the rounding policy of the current optimization trial.

  Parameters
  ----------
  roundDict : dict
    Rouncing policy for the different parameters.
  gene : dict
    Gene to be rounded.

  Returns
  -------
  dict
    Rounded gene.
  """
  for k in gene:
    if k == "fitness": continue
    # compute the rounding
    target = 0
    if roundDict[k] > 1:
      while 10**target < roundDict[k]: target += 1
    else:   
      while 10**target > roundDict[k]: target -= 1
    gene[k] = round(gene[k],-target)
  return gene


def statGAselect(inPop):
  """
  Selects a gene depending on its fitness. Lower values of fitness have a higher chance of being selected.
  The function used is 1/f for f being the fitness
  
  Parameters
  ----------
  inPop : list
    Population of genes.

  Returns
  -------
  dict
    Selected gene.
  """
  sumFit = sum([ 1.0/g["fitness"] for g in inPop])
  i = -1
  while (sumFit > 0) and (i < len(inPop)-1):
    i += 1
    sumFit -= inPop[i]["fitness"]
  return inPop[i].copy()  
  

def statGAmutate(roundDict, gene, fixedParams, extremeMutation=False):
  """
  Mutates the given gene according to the values in round Dict.

  Parameters
  ----------
  roundDict : dict
    Rounding policy of the current optimization strategy.
  gene : dict
    Parameters for the current optimization problem.
  fixedParams : set
      Makes some parameters immutable. Gives them as an element of the set each.  
  extremeMutation : bool
    Increases mutation by an order of magnitute  
    

  Returns
  -------
  dict
    New gene after mutation, could also be the same gene, unmutated.
  """
  outGene = gene.copy()
  for k in gene:
    if k == "fitness": continue
    if k in fixedParams: continue
    if extremeMutation: outGene[k] = gene[k] + random.randint(-20,20)*roundDict[k]
    if random.randint(0,10) != 0: continue
    outGene[k] = gene[k] + random.randint(-10,10)*roundDict[k]
  return outGene  
  


def statGAcrossoverUniform(p1,p2):
  """
  Uses the crossover strategy to create two children for the two given parents.

  Parameters
  ----------
  p1 : dict
    Gene. First parent.
  p2 : dict
    Gene. Second parent.

  Returns
  -------
  c1 : dict
    First child.
  c2 : dict
    Second child.
  """
  c1 = {}; c2 = {}
  for k in p1:
    if k == "fitness": continue
    if random.randint(0,1) == 0: c1[k] = p1[k]; c2[k] = p2[k]
    else: c1[k] = p2[k]; c2[k] = p1[k]
  return c1,c2


def statGAcrossoverAverage(p1,p2, fixedParams):
  """
  Computes the average between the parameters of the two parents.

  Parameters
  ----------
  p1 : dict
    Gene. First parent.
  p2 : dict
    Gene. Second parent.
  fixedParams : set
    Makes some parameters immutable. Gives them as an element of the set each.  
  
  Returns
  -------
  c : dict
    Only child.
  """
  c = {}
  for k in p1:
    if k == "fitness": continue
    c[k] = (p1[k] + p2[k]) / 2 if not k in fixedParams else p1[k] # avoid rounding errors
  return c


def statGAgene2key(gene):
  """
  Generates a unique hash value for each gene. The fitness value is excluded.

  Parameters
  ----------
  gene : dict
    Parameters for the optimization problem.

  Returns
  -------
  str
    Hash for the current gene.
  """
  sortKeys = []
  allKeys = filter(lambda x: x != "fitness", gene.keys())
  for k in allKeys: sortKeys.append(k)
  sortKeys.sort()
  # create a key
  return "; ".join( [ k+"="+str(gene[k]) for k in sortKeys ] )
  

def statGArun(onlyMutate = False, fixedParams=set(),maxVals={}):  
  """
  Executes the optimization algorithm for statistical data. All results are written to a file.
  Using the switch "onlyMutate", it can be turned into a Evolutionary Strategy (ES)

  Params
  ------
    onlyMutate : bool
      Do not use the crossover operator in the algorithm, no extreme mutation.
    fixedParams : set
      Makes some parameters immutable. Gives them as an element of the set each.  
    maxVals : dict
      maximal values for the optimization

  Returns
  -------
  None
  """
  wm = "Dp,3"
  wm = statGAsplitWM(wm)
  allData, allLabel = statGiveData(wm)
  trainingData = avgLists(allData)
  trainingLabel = allLabel[0].split(",",1)[0] + ", avg"
  
  maxRun = 1000; popSize = 1000; bestLen = 20
  
  prefix = "statGA"; outStr = ""; intState = {}
  outStr += "Params: "+ str(trainingLabel)
  plotState(prefix, intState, outStr)
  
  oldPop = [ ]
  startGene,roundDict = statGAgiveInitialGene(wm)
  startGene["fitness"] = statGAfitness(wm, trainingData, startGene)

  # start with an intitial population  
  for i in range(popSize): 
    # no extreme mutation if we are in an ES
    g = statGAmutate(roundDict, startGene, fixedParams, extremeMutation=not(onlyMutate))
    g = statGAroundGene(roundDict, g)
    g["fitness"] = statGAfitness(wm, trainingData, g)
    if str(g["fitness"]) != "nan": oldPop.append(g)
  
  # initialize the loop
  bestList = []
  
  runNum = -1
  toRun = True
  while toRun:
    runNum += 1
    # create a newPop
    newPop = []
    
    for i in range(popSize):
      p1 = statGAselect(oldPop)
      p2 = statGAselect(oldPop)
      
      c1 = statGAmutate(roundDict, p1, fixedParams)
      newPop.append(c1)
      if not(onlyMutate):
        c2,c3 = statGAcrossoverUniform(p1,p2)
        c4 = statGAcrossoverAverage(p1,p2, fixedParams)
        newPop.append(c2)
        newPop.append(c3)
        newPop.append(c4)
    # remove too high values
    for g in newPop:
      for k in maxVals:
        if g[k] > maxVals[k]: g[k] = maxVals[k]
    # make sure they are correctly rounded
    for i in range(len(newPop)):
      n = newPop[i]
      n = statGAroundGene(roundDict, n)
      n["fitness"] = statGAfitness(wm, trainingData, n)
      newPop[i] = n
    # end generating new population
    
    # add the two lists together, sort them by fitness and remove doublicates
    curPop = newPop
    # Remove unwanted and double entries
    curPop = filter(lambda g: str(g["fitness"]) != "nan", curPop)
    noDouble = {}
    for g in curPop: noDouble[statGAgene2key(g)] = g
    curPop = [ noDouble[k] for k in noDouble ]
    # sort
    curPop.sort(key=lambda g: g["fitness"])
    
    oldPop = curPop[:popSize]
    # keep our best results 
    bestList.append(oldPop[0])
    bestList.sort(key=lambda g: g["fitness"])
    bestList = bestList[:bestLen]
    outStr += "\n New List for run {} and {} \n".format(runNum,trainingLabel)
    for p in bestList:
      outStr += str(p) + "\n"
    plotState(prefix, intState, outStr)  
    
    # check if we can leave the loop
    if (statGAgene2key(bestList[0]) == statGAgene2key(bestList[-1])) and (bestLen == len(bestList)): toRun = False
    if runNum > maxRun: toRun = False
  print("Done gaStat")


def statPaint():
  # s = 3
  # Run 873 and s=3, avg - fitted
  #param = {'weight': 0.5913999999999997, 
  #         'pGuessOne': 0.7647999999999996, 'stretchOne': 14127, 'locOne': 0.0, 'nGuessOne': 34.0, 
  #         'pGuessTwo': 0.27179999999999943, 'stretchTwo': 9758, 'locTwo': 0.0, 'nGuessTwo': 34.0, 
  #         'fitness': 55644.72874865864}
  # s=3, avg - manual
  #param = {'weight': 0.5914, 
  #         'pGuessOne': 0.6200, 'stretchOne': 14000, 'locOne': 0.0, 'nGuessOne': 40.0, 
  #         'pGuessTwo': 0.3000, 'stretchTwo': 8000, 'locTwo': 0.0, 'nGuessTwo': 40.0, 
  #         'fitness': 55644.72874865864}

  # b, s=5 manual
  #wm = "b,5"
  #param = {'pGuess': 0.5000, 'stretch': 2200, 'loc': -7, 'nGuess': 23.0, 'fitness': 5930}  
  # New List for run 165 and n=5, avg 
  # b5 - fitting
  #param = {'pGuess': 0.5073, 'stretch': 2330, 'loc': -7, 'nGuess': 23.0, 'fitness': 4057.7813736216544}
  
  # p, s=5 fitting
  #wm = "p,5"
  #param = {'stretch': 2940, 'mu': 9.0, 'loc': -4, 'fitness': 33.188104337711664}
  # p, 7 - manual
  #wm = "p,7"
  #param = {'stretch': 2488, 'mu': 7.100000000000001, 'loc': -9, 'fitness': 41.45823453369279}
  # p,7 - fitting
  #param = {'stretch': 2900, 'mu': 6.82, 'loc': -9, 'fitness': 39.17969322200599}
  # b,7 - manual
  #param = {'pGuess': 0.5000, 'stretch': 600, 'loc': -2, 'nGuess': 4.0}
  # b,7 - fitting - New List for run 279 and n=7, avg 
  #wm = "b,7"
  #param = {'pGuess': 0.2822, 'stretch': 1460, 'loc': -7, 'nGuess': 23.0, 'fitness': 18.079273942319123}
  
  # Dp, s=3, fitting
  wm = "Dp,3"
  #param = {'fitness': 74171.19640282032, 'weight': 0.5991, 'stretchOne': 10005, 'muOne': 10.809999999999999, 'locOne': 0, 'stretchTwo': 10016, 'muTwo': 18.389999999999983, 'locTwo': 10}
  # Dp3, manual
  #param = {'stretchOne': 3000, 'muOne': 11.549999999999997, 'locOne': 1, 
  #         'stretchTwo': 10137, 'muTwo': 17.969999999999978, 'locTwo': 7}
  # Dp3, manual 
  param = {'stretchOne': 2400, 'muOne': 5.09, 'locOne': 7, 
           'stretchTwo': 9100, 'muTwo': 17.36, 'locTwo': 7, 'fitness': 98980.64767731426}  
  # intermediate fitting I 
  param = {'stretchOne': 2465, 'muOne': 5.01, 'locOne': 5, 
           'stretchTwo': 9081, 'muTwo': 17.24, 'locTwo': 7, 'fitness': 41416.60648706726}
  # fitting I - 0.01 mu
  param = {'stretchOne': 2500, 'muOne': 4.97, 'locOne': 5, 
           'stretchTwo': 9850, 'muTwo': 17.2, 'locTwo': 7, 
           'fitness': 41189.4915289946}
  # manual I - 0.01 mu
  param = {'stretchOne': 2700, 'muOne': 6.97, 'locOne': 5, 
           'stretchTwo': 9850, 'muTwo': 18.2, 'locTwo': 7}

  # Db3 - manual
  wm = "Db,3"
  # Db3 - manual
  param = {'pGuessOne': 0.6795, 'stretchOne': 7000, 'locOne': 0.0, 'nGuessOne': 37.0, 
           'pGuessTwo': 0.2697, 'stretchTwo': 3500, 'locTwo': 0.0, 'nGuessTwo': 50.0, 
           'fitness':  85495575123867.28}
  
  
  # Sp, s=3, manual
  #param = {'split': 17, 'stretchOne': 3300, 'muOne': 13, 'locOne': -1.0, 
  #                      'stretchTwo': 5000, 'muTwo': 7, 'locTwo': 0, 'fitness': -1,}
  # Sp, s=3, fitting
  #param = {'split': 18, 'stretchOne': 3329, 'muOne': 13.529999999999998, 'locOne': -3.0, 
  #                      'stretchTwo': 5157, 'muTwo': 7.01, 'locTwo': 0, 'fitness': 47479.63173918127}
  # Sp, s=3, fitting
  #param = {'split': 20, 'stretchOne': 4257, 'muOne': 14.659999999999997, 'locOne': -3.0, 
  #                      'stretchTwo': 6720, 'muTwo': 7.939999999999997, 'locTwo': -2.0, 'fitness': 9583.791513065386}
  
  # Sb,3 - manual
  #param = {'split': 17, 
  #         'pGuessOne': 0.5000, 'stretchOne': 3000, 'locOne': -10, 'nGuessOne': 40.0, 
  #         'pGuessTwo': 0.3000, 'stretchTwo': 6000, 'locTwo': -4.0, 'nGuessTwo': 40.0, 
  #         'fitness': -1}
  # Sb,3 - fitting run 229
  #param = {'split': 18, 'pGuessOne': 0.5016, 'stretchOne': 3471, 'locOne': -10.0, 'nGuessOne': 41.0, 
  #         'pGuessTwo': 0.263, 'stretchTwo': 7844, 'locTwo': -4.0, 'nGuessTwo': 45.0, 'fitness': 15797}

  
  
  wm = statGAsplitWM(wm)
  allData, allLabel = statGiveData(wm)
  trainingData = avgLists(allData)
  trainingLabel = allLabel[0].split(",",1)[0] + ", avg"
  
  # for k in range(len(allData)):
  #   plt.plot(range(len(allData[k])), allData[k], label=allLabel[k])

  # prediction = [ statGAfitness(wm, trainingData, param,x) for x in range(len(trainingData)) ]

  # plt.plot(range(len(trainingData)), trainingData, "co", label=trainingLabel)  
  # plt.plot(range(len(prediction)), prediction, "k^", label="prediction")  
  # plt.legend(title="With parameters")
  
  # print("Fitness: {}".format(statGAfitness(wm, trainingData, param)))
  # plt.show()
  


#########################################################################
# printing
def paramsUOV():
  """
  Check and outputs possible parameters for UOV

  Returns
  -------
  None.
  """
  # n,v
  menue = [ [113,68], [161,96], [185,112], [245,148] ]
  for tup in menue:
    n = tup[0]; v = tup[1]
    termsPub = n * (n+1) / 2
    if ( termsPub % 2) == 0: print("problem n={}".format(n))
    if ( (n-v) % 2) == 0: print("problem n={}, v={}".format(n,v))
    print(" & & {} & {} & {} & 1 & ".format(n,v,n-v))

  
def printDef():
  for filename in ["flipFields.py"]:
    print("-------------------------------------------")
    print("Filename: "+filename)
    with open(filename, "r", encoding="utf-8") as f:
      curLine = f.readline()
      while curLine:
        print(curLine+"---end")
        if curLine[0:2] == "def": print(curLine)
    f.close()   
  
  
############################################################################
# Unit Testing
def testAll():
  """
  Unit Testing for this file

  Returns
  -------
  None.

  """
  print("Start Testing flipFields")

  if isField(1): print("Error isField.1")
  if isField(-1): print("Error isField.2")
  if isField(5): print("Error isField.3")
  if not(isField(4)): print("Error isField.4")
  if not(isField(512)): print("Error isField.5")

  if isElem(2,4): print('Error isElem.1')
  if isElem(3,5): print('Error isElem.2')
  if not(isElem(3,8)): print('Error isElem.3')


  # poly2num & num2poly
  A = {1:1, 0:1}  
  res = poly2num(A,16)
  assert res == 17, "Error poly2num.1 %d"+str(res)
  aDash = num2poly(res,16)
  assert aDash == A, "Error num2poly.1 %d"+str(aDash)
  A = {1:3, 0:1}  
  res = poly2num(A,16)
  assert res == 49, "Error poly2num.2 %d"+str(res)
  aDash = num2poly(res,16)
  assert aDash == A, "Error num2poly.2 %d"+str(aDash)
  A = {2:1, 0:1}  
  res = poly2num(A,16)
  assert res == 257, "Error poly2num.3 %d"+str(res)
  aDash = num2poly(res,16)
  assert aDash == A, "Error num2poly.3 %d"+str(aDash)
  A = {2:5, 0:7}  
  res = poly2num(A,16)
  assert res == 5*256+7, "Error poly2num.4 %d"+str(res)  
  aDash = num2poly(res,16)
  assert aDash == A, "Error num2poly.4 %d"+str(aDash)
  
  # ga-routines
  res = list2strMulti([1])
  assert res == "#", "Error list2strMulti.1 !%s!"%res
  res = list2strMulti([1,2])
  assert res == "2", "Error list2strMulti.2 !%s!"%res
  res = list2strMulti([1,2,3])
  assert res == "2#3", "Error list2strMulti.3 !%s!"%res
  res = list2strMulti([1,3,2])
  assert res == "2#3", "Error list2strMulti.4 !%s!"%res
  res = list2strMulti([1,3,0,2])
  assert res == "0#2#3", "Error list2strMulti.5 !%s!"%res
  
  
  res = isMultiPoly({'#': 1, '1':3, '2':5},3,10,16)
  assert res, "Error isMultiPoly.1"
  res = isMultiPoly({'#': 1, '1':2, '2':5},3,10,16)
  assert not(res), "Error isMultiPoly.2"
  res = isMultiPoly({'#': 1, '1':3, '2':5},3,1,16)
  assert not(res), "Error isMultiPoly.3"
  res = isMultiPoly({'#': 0, '1':3, '2':5},3,10,16)
  assert not(res), "Error isMultiPoly.4"
  res = isMultiPoly({'#': 1, '1':3, '2#2':5},3,10,16)
  assert res, "Error isMultiPoly.5"
  res = isMultiPoly({'#': 1, '1':3, '1#2#1':5},4,10,16)
  assert not(res), "Error isMultiPoly.6"
  res = isMultiPoly({'#': 1, '1':3, '1#2#3':5},2,10,16)
  assert not(res), "Error isMultiPoly.7"
  
  res = applyMultiPoly({'#':1}, [1,3,5],16)
  assert res == 1, "Error applyMultiPoly.1 with {}".format(res)
  res = applyMultiPoly({'#':3}, [1,3,5],16)
  assert res == 3, "Error applyMultiPoly.2 with {}".format(res)
  res = applyMultiPoly({'1':7}, [1,3,5],16)
  assert res == 5, "Error applyMultiPoly.3 with {}".format(res)
  res = applyMultiPoly({'0':7}, [1,3,5],16)
  assert res == 7, "Error applyMultiPoly.4 with {}".format(res)
  res = applyMultiPoly({'0#2':1}, [1,3,5],16)
  assert res == 5, "Error applyMultiPoly.4 with {}".format(res)
  res = applyMultiPoly({'0#2':1, '1':3, '#':1}, [1,3,5],16)
  assert res == 15, "Error applyMultiPoly.5 with {}".format(res)
  res = applyMultiPoly({'0#2':1, '1#2':7, '0':11, '1':3, '#':1}, [1,3,5],16)
  assert res == (131 % 16), "Error applyMultiPoly.6 with {}".format(res)
  
  # pretty printing for multivariate polynomials
  res = multiPoly2strPretty({'#':1})
  assert "1" == res, "Error multiPoly2strPretty.1 with "+res
  res = multiPoly2strPretty({'#':7})
  assert "7" == res, "Error multiPoly2strPretty.2 with "+res
  res = multiPoly2strPretty({'#':1, '2':5, '12':3, "1#2":7})
  assert "7x_{1}x_{2}+3x_{12}+5x_{2}+1" == res, "Error multiPoly2strPretty.3 with "+res
  res = multiPoly2strPretty({'#':1, '2':5, '12':3, '1#3#4':5, '3#4#5':5, '6#7#8':5, "1#2":7})
  assert "5x_{6}x_{7}x_{8}+5x_{3}x_{4}x_{5}+5x_{1}x_{3}x_{4}+7x_{1}x_{2}+3x_{12}+5x_{2}+1" == res, "Error multiPoly2strPretty.4 with "+res
  res = multiPoly2strPretty({'#':1, '2':1, '12':1, "1#2":1})
  assert "x_{1}x_{2}+x_{12}+x_{2}+1" == res, "Error multiPoly2strPretty.3 with "+res
  
  # check average list
  x = avgLists([ [1,2,3], 
                 [1,2,3] ])
  assert x == [1.0, 2.0, 3.0], "avgLists.1 with {}".format(x)
  x = avgLists([ [1,2,3,5], 
                 [1,2,3] ])
  assert x == [1.0, 2.0, 3.0, 5.0], "avgLists.2 with {}".format(x)
  
  # verify if we produce the same sequences in the univariate and the multivariate case
  outNum = 500
  D = 16
  tests = []
  
  testItem = {}
  testItem["N"] = 3
  testItem["p"] = {'0':3,'1':1, '2':5}
  testItem["R"] = {  0:3,  1:1,   2:5,   3:1}
  tests.append(testItem.copy())
  testItem["N"] = 5
  testItem["p"] = {'1':5, '3':1,'4':1}
  testItem["R"] = {  1:5,   3:1,  4:1,    5:1}  
  tests.append(testItem.copy())
  testItem["N"] = 7 
  testItem["p"] = {'0':3,'1':5, '2':5,'3':1,'4':1}
  testItem["R"] = {  0:3,  1:5,   2:5,  3:1,  4:1,    7:1}
  tests.append(testItem.copy())
  testItem["N"] = 7
  testItem["p"] = {     '4':1, '2':1, '0':1}
  testItem["R"] = {7:1,   4:1,   2:1,   0:1}
  tests.append(testItem.copy())
  testItem["N"] = 10
  testItem["p"] = {'0':3,'1':1, '2':5,'3':1, '7':5}
  testItem["R"] = {  0:3,  1:1,   2:5,  3:1,   7:5,   10:1}
  tests.append(testItem.copy())
  testItem["N"] = 16 
  testItem["p"] = {'0':3,'1':5, '2':5,'3':1, '7':5,'11':1, '12':5}
  testItem["R"] = {  0:3,  1:5,   2:5,  3:1,   7:5,  11:1,   12:5,   16:1}
  tests.append(testItem.copy())  
  testItem["N"] = 128
  testItem["p"] = {'0':3,'1':5, '2':5,'3':1, '7':5,'11':1, '127':5}
  testItem["R"] = {  0:3,  1:5,   2:5,  3:1,   7:5,  11:1,   127:5,   128:1}
  tests.append(testItem.copy())

  for i in range(len(tests)):
    curTest = tests[i]
    N = curTest["N"]; p = curTest["p"]; R = curTest["R"]
    stateMulti = [1] * N
    stateUni = {i:1 for i in range(N)}
    cUni = []; cMulti = []
    for i in range(outNum):
      newValMulti = applyMultiPoly(p,stateMulti,D)  
      stateMulti.pop(0); stateMulti.append(newValMulti)
      stateUni = polyFibStep(stateUni,R,D)
      cUni.append(stateUni[0]); cMulti.append(stateMulti[0])
    assert cUni == cMulti, "uniMulti tstCase={} not equal for {}".format(i,curTest)
    
  print("End testing flipFields")  


#testAll()

 
      







