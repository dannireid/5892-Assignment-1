// Assignment 1 - 5892
// Question 1
// Authors: Danielle Reid (201729019), Andrew Troake (201711165)

predicate Sorted( s : seq<int> )
{
    forall i,j : int :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}

predicate PermutationOf( s : seq<int>, t : seq<int> )
{
    multiset(s) == multiset(t)
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
    // ensures Sorted( a[..] )
    // ensures PermutationOf( old(a[..]), a[..] )
{
    var j := 0;
    var last := a.Length - j - 1;

    while ( j < a.Length )
        invariant 0 <= j <= a.Length
        invariant Sorted( a[last..] )
        // invariant PermutationOf( old(a[..]), a[..] )
        decreases a.Length - j
    {
        var k := 0;
            
        while ( k < j )
            invariant 0 <= k <= j
            decreases j - k
        {
            if( a[k] > a[j] )
            {
                a[k], a[j] := swap(a[k], a[j]);
            }
                
            k := k + 1;
        }
        
        j := j + 1;
        last := a.Length - j;
    }
}

method Main()
{
    // Test:
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 6, 2, 1, 9, 3;
    bubbleSort(a);

    var i := 0;
    while ( i < a.Length )
    {
        print a[i], "\t";
        i := i + 1;
    }
}