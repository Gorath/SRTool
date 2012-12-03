void main(int i, int j, int k, int l)
{
	i=1;
	j=2;
	k=3;
	l=-4;

	int p;
	int q;
	int r;

	p = i * j + k / j;
	q = p - j;
	r = l / (-i * l);

    assert(p == 3);
    assert(q == 1);
    assert(r == -1);
}
