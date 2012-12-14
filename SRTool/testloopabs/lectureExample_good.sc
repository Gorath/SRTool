void main (int x){

    int i;
    i = 0;

    assume (i==x);

    while (i < x)
        inv(i >= 0 && i >= x)
        {
        assert(i >= 0);
        i = i+1;

    }
    assert(i==x);
}
