void main(int i, int j, int k)
{
	i=1;
	j=2;
	k=3;

	int p;
	int q;
	int r;

	p = i * j + k / j;
	q = p - j;

    assert(p == 3);
    assert(q == 1);
}
