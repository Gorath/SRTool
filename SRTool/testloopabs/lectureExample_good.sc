void main (int x){

    int i;
    i = 0;

    assume (i==x);

    while (i < x)
        inv(i == x)
    {
        assert(i >= 0);
        i = i+1;
        assume (0);

    }

    assert(i==x);
}
