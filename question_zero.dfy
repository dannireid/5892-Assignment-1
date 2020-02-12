// Assignment 1 - 5892
// Question 0
// Authors: Danielle Reid (201729019), Andrew Troake (201711165)

predicate Sorted( s : seq<int> )
{
    forall i,j : int :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}

method binarySearch( t : int, a : seq<int> ) returns ( result : int )
    requires Sorted( a[..] )
    ensures t in a ==> result >= 0
    ensures t !in a ==> result == -1
{
    var p := 0;
    var r := |a|;

    while ( r - p >= 2 )
        invariant 0 <= p <= r <= |a|
        invariant t in a[..] ==> t in a[p..r]
        decreases r - p
    {
        var q := (p + r) / 2;

        if (a[q] <= t)
        {
            p := q;
        }
        else if (a[q] > t)
        {
            r := q;
        }
    }

    if ( p == r )
    {
        result := -1;
    }
    else if (t == a[p])
    {
        result := p;
    }
    else
    {
        result := -1;
    }

    return result;
}

method Main() {
    // Test 1:
    var a := new int[4];
    a[0], a[1], a[2], a[3] := 1, 3, 5, 81;
    var find := 3;
    var result := binarySearch(find, a[..]);

    // Test 2:
    find := 9;
    result := binarySearch(find, a[..]);
}