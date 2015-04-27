/*
Given: An integer array a of length n+2 with n>=2. It is known that at
least two values stored in the array appear twice (i.e., there are at
least two duplets).

Implement and verify a program finding such two values.

You may assume that the array contains values between 0 and n-1.
*/

method duplet(a:array<int>, oldDuplet: int) returns (newDuplet: int)
requires a!= null;
requires a.Length >= 2;
requires exists k, l:: 0 <= k < l < a.Length && a[k] == a[l] && a[k] != oldDuplet;
ensures exists k, l:: 0 <= k < l < a.Length && a[k] == newDuplet && a[k] == a[l] && newDuplet != oldDuplet;
{
	newDuplet := -1;
	var i:int := 0;
  	while (i < a.Length-1)
  	invariant 0 <= i <= a.Length-1;
    invariant exists k, l:: i <= k < l < a.Length && a[k] == a[l] && a[k] != oldDuplet;
 	{	
 	    if a[i] != oldDuplet
		{		
 			var j := i + 1;
 			while (j < a.Length)
 			decreases a.Length - j;
 			invariant 0 <= i < a.Length;
 			invariant i+1 <= j <= a.Length;
 		    decreases a.Length - i;
 	    	invariant forall k:: i < k < j ==> a[i] != a[k];
			{
 	    		if a[i] == a[j]
 	    		{
 	    			newDuplet := a[i];
 	    			return;
 	    		}
 	    		j := j + 1;
 	    	}
 	    	
 	    }
 	    i := i + 1;		
	}
}

method duplets(a:array<int>) returns (duplet1: int, duplet2: int)
requires a!= null;
requires a.Length >= 4;
requires exists k, l:: 0 <= k < l < a.Length && a[k] == a[l]
      && exists kk, ll:: 0 <= kk < ll < a.Length && a[kk] == a[ll] && a[kk] != a[k];
ensures duplet1 != duplet2;
ensures exists k, l:: 0 <= k < l < a.Length && a[k] == duplet1 && a[k] == a[l];
ensures exists k, l:: 0 <= k < l < a.Length && a[k] == duplet2 && a[k] == a[l];
{
	duplet1 := duplet(a, -1);
	duplet2 := duplet(a, duplet1);
}

method Main() 
{
  var a := new int[4];
  a[0] := 1;
  a[1] := 2;
  a[2] := 1;
  a[3] := 2;
  
  var duplet1:int := 0;
  var duplet2:int := 0;
  duplet1, duplet2 := duplets(a);
  print "duplet1=", duplet1;
  print " duplet2=", duplet2;

}
