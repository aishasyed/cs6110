/*
Sum and Max: Given an n-element array 'a', computes the sum and 
			 maximum of its elements.
Properties:  Given n >= 0 and a[i] >= 0 for 0 <= i < n
             prove the post-condition that sum <= n * max
*/

method SumMax(a: array<int>) returns (max: int, sum: int)
  requires a != null;
  requires forall k:: 0 <= k < a.Length ==> a[k] >= 0;
  ensures sum <= a.Length * max;
{
	sum := 0;
	max := 0;
	
	var i:int := 0;
	while (i < a.Length)
	invariant 0 <= i <= a.Length;
	invariant sum <= i * max;
	{
		if (max < a[i])
		{
			max := a[i];
		}
		sum := sum + a[i];
		i := i + 1;
	}
}

method Main() 
{  
  var a := new int[10];
  a[0] := 9;
  a[1] := 5;
  a[2] := 0;
  a[3] := 2;
  a[4] := 7;
  a[5] := 3;
  a[6] := 2;
  a[7] := 1;
  a[8] := 10;
  a[9] := 6;
  //sum should be (9+ 5+ 0+ 2+ 7+ 3+ 2+ 1+ 10+ 6) = 45;
  
  var sum:int := 0;
  var max:int := 0;
  max, sum := SumMax(a);
  print "max=", max;
  print " sum=", sum;  
  
  //prints correct max and sum of array: max=10 sum=45 
  
}
