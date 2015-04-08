/*
Given: An integer array a of length n+2 with n>=2. It is known that at
least two values stored in the array appear twice (i.e., there are at
least two duplets).

Implement and verify a program finding such two values.

You may assume that the array contains values between 0 and n-1.

*/

method count(num:int, a:array<int>) returns (countN: int)
requires a!= null;
{
	countN := 0;
	var i:int := 0;
  	while (i < a.Length)
  	{
  		if a[i] == num
  		{
  			countN := countN + 1;
  		}
    	i := i + 1;
  	}
}

function total(a: array<int>, i:int, key: int): int
requires a != null;
reads a;
{
	if i < 0
  		then 0
 	else if (a.Length == 0)
  		then 0
  	else if 0<=i<a.Length && a[i] == key
  		then total(a, i-1, key) + 1
  	else total(a, i-1, key)
}

predicate check(a: array<int>, key: int)
reads a;
requires a != null;
{
	total(a, a.Length, key) >= 2
}

method duplets(a:array<int>) returns (num1: int, num2: int)
requires a!= null;
requires a.Length >= 4;
ensures check(a, num1);
//ensures forall k:: forall l:: 0 <= k < l < a.Length ==> a[k] <= a[l];
{
	num1 := -1;
	num2 := -1;
	var numPtr:int := 1;

	var i:int := 0;
  	while (i < a.Length && numPtr == 1)
	{	
		var c:int := 0;
		var current := a[i];
		c := count(current, a);
		i := i + 1;
		
		if c >= 2
		{
			num1 := current;
			numPtr := 2;
			break;
		}		 
	}
	
	while (i < a.Length && numPtr == 2)
	invariant num1 > -1;
	{	
		var c:int := 0;
		var current := a[i];
		c := count(current, a);
		i := i + 1;
		
		if c >= 2
		{
			num2 := current;
			numPtr := 3;
			break;
		}		 
	}
}

method Main() 
{
  var countN:int := 0;
  var a1 := new int[4];
  a1[0] := 1;
  a1[1] := 2;
  a1[2] := 1;
  a1[3] := 2;
  
  var num1:int := 0;
  var num2:int := 0;
  num1, num2 := duplets(a1);
  print "num1=", num1;
  print " num2=", num2;
}
