void main()
{
	int start;
	int i;
	i=start;

	if (i > 0) {

	    while(i > 0)
	    bound(3)
	    {
	        i = i - 1;
	    }

	} else {

	    while(i < 0)
	    bound(3)
	    {
	        i = i + 1;
	    }

	}

	// without unwinding assertions, this assert failure should be missed

	if(start > 2 || start < -2)
	{
		assert(0);
	}

}
