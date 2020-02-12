// Assignment 1 - 5892
// Question 1
// Authors: Danielle Reid (201729019), Andrew Troake (201711165)

predicate Sorted( a : array<int>, start : int, end : int )
    reads a
{
    forall i, j :: 0 <= start <= i <= j <= end < a.Length ==> a[i] <= a[j]
}

predicate Partitioned( a : array<int>, i : int )
    reads a
{
    forall k, k' :: 0 <= k <= i < k' < a.Length ==> a[k] <= a[k']
}

method swap( a : int, b : int ) returns ( c : int, d : int )
    ensures c == b
    ensures d == a
{
    c := b;
    d := a;
    return c, d;
}

method bubbleSort( a : array<int> )
    modifies a
    ensures Sorted(a, 0, a.Length - 1)
{
    var j := a.Length - 1;

    while(j > 0)
        invariant j < 0 ==> a.Length == 0
        invariant Sorted(a, j, a.Length - 1)
        invariant Partitioned(a, j)
        decreases j
    {
        var k := 0;

        while (k < j)
            invariant 0 < j < a.Length
            invariant 0 <= k <= j
            invariant Sorted(a, j, a.Length - 1)
            invariant Partitioned(a, j)
            invariant forall m :: 0 <= m <= k ==> a[m] <= a[k]
            decreases j - k
        {
            if( a[k] > a[k + 1] )
            {
                a[k], a[k + 1] := swap(a[k], a[k + 1]);
            }
            
            k := k + 1;
        }

        j := j - 1;
    }
}
  
method Main() {
    // Test 1:
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 10, 4, 5, 7, 8;
    bubbleSort(a);
    var k := 0;
    print "Test 1: ";
    while ( k < a.Length )
      decreases a.Length - k
    {
        print a[k], "\t";
        k := k+1;
    }

    // Test 2:
    a[0], a[1], a[2], a[3], a[4] := 4, 5, 6, 122, 8;
    bubbleSort(a);
    k := 0;
    print "\nTest 2: ";
    while ( k < a.Length )
      decreases a.Length - k
    {
        print a[k], "\t";
        k := k+1;
    }
}