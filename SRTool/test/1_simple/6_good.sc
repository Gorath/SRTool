void main(int i, int j, int k)
{
	i=20;
	j=18;
	k=18;

	int p;
	int q;
	int r;
	int s;
	int t;

	p = (j < i);
	q = (j <= k);
	r = (j >= k);
	s = (i >= k);
	t = (i > k);

	assert(p);
	assert(q);
	assert(r);
	assert(s);
	assert(t);
}
