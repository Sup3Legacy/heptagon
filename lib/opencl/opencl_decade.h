#ifndef OPENCL_COMMON_H
#define OPENCL_COMMON_H

#if defined __APPLE__ || defined(MACOSX)
    #include <OpenCL/opencl.h>
#else
    #include <CL/opencl.h>
#endif

typedef struct {
  cl_platform_id platform;

  //device variables
  cl_device_id* devices;
  cl_uint numDevices;
  unsigned int deviceUsed;

  cl_context context;

  cl_command_queue command_queue;

  //debugging variables
  cl_event event;

  cl_uint max_compute_units;
  size_t max_work_item_sizes;
  size_t max_work_group_size;
  cl_ulong max_global_mem_size;

  cl_int err;
  cl_program program;
} opencl_environment;

opencl_environment *cl_init_gpu(void);
void cl_destroy(opencl_environment *ev);

cl_program cl_load_program(opencl_environment *ev, const char *include_path, 
                       const char *filename, const char *compile_flags);

#endif
