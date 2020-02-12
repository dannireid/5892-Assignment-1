// Assignment 1
// Question 1
// Danielle Reid (201729019), Andrew Troake (201711165)


method swap(a:int, b:int)
returns (c:int,d:int)
    ensures c == b && d == a
{
    var temp := a;
    a := b;
    b := temp;
    return a,b;
}

method bubblesort(a:array<int>, i:int)
returns (a2:array<int>)
    requires i > 0
    ensures Sorted(a) && PermutationOf(a, a1)
    var j := 0;
    while j < i

    {
        smallest := a(j);
        var k := j+1;
        while(k < i)
            invariant j < i
            invariant k > j
        {
            if(a(k) < a(j)){
                a(k),a(j) := swap(a(k), a(j));
            }
            k := k+1;
        }
        j := j+1;
    }
    return a;
}

method main(){
    var a := new int[5];
    a[0],a[1],a[2],a[3],a[4] := 6,2,1,9,3;
    a := bubblesort(a, 5);
    print a;
}