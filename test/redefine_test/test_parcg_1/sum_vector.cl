__kernel void vector_add(__global const int *a, __global const int *b, __global int *c) {
    // Get the index of the current element to be processed
    int i = get_global_id(0);

    // Do the operation (in a non-effective way, but it still does the job)
    c[i] = a[i] + b[i];
}
