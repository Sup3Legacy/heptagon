#include "opencl_decade.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#if defined __APPLE__ || defined(MACOSX)
    #include <OpenCL/opencl.h>
#else
    #include <CL/opencl.h>
#endif

static const char* error_string[] = {
    "CL_SUCCESS",
    "CL_DEVICE_NOT_FOUND",
    "CL_DEVICE_NOT_AVAILABLE",
    "CL_COMPILER_NOT_AVAILABLE",
    "CL_MEM_OBJECT_ALLOCATION_FAILURE",
    "CL_OUT_OF_RESOURCES",
    "CL_OUT_OF_HOST_MEMORY",
    "CL_PROFILING_INFO_NOT_AVAILABLE",
    "CL_MEM_COPY_OVERLAP",
    "CL_IMAGE_FORMAT_MISMATCH",
    "CL_IMAGE_FORMAT_NOT_SUPPORTED",
    "CL_BUILD_PROGRAM_FAILURE",
    "CL_MAP_FAILURE",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "",
    "CL_INVALID_VALUE",
    "CL_INVALID_DEVICE_TYPE",
    "CL_INVALID_PLATFORM",
    "CL_INVALID_DEVICE",
    "CL_INVALID_CONTEXT",
    "CL_INVALID_QUEUE_PROPERTIES",
    "CL_INVALID_COMMAND_QUEUE",
    "CL_INVALID_HOST_PTR",
    "CL_INVALID_MEM_OBJECT",
    "CL_INVALID_IMAGE_FORMAT_DESCRIPTOR",
    "CL_INVALID_IMAGE_SIZE",
    "CL_INVALID_SAMPLER",
    "CL_INVALID_BINARY",
    "CL_INVALID_BUILD_OPTIONS",
    "CL_INVALID_PROGRAM",
    "CL_INVALID_PROGRAM_EXECUTABLE",
    "CL_INVALID_KERNEL_NAME",
    "CL_INVALID_KERNEL_DEFINITION",
    "CL_INVALID_KERNEL",
    "CL_INVALID_ARG_INDEX",
    "CL_INVALID_ARG_VALUE",
    "CL_INVALID_ARG_SIZE",
    "CL_INVALID_KERNEL_ARGS",
    "CL_INVALID_WORK_DIMENSION",
    "CL_INVALID_WORK_GROUP_SIZE",
    "CL_INVALID_WORK_ITEM_SIZE",
    "CL_INVALID_GLOBAL_OFFSET",
    "CL_INVALID_EVENT_WAIT_LIST",
    "CL_INVALID_EVENT",
    "CL_INVALID_OPERATION",
    "CL_INVALID_GL_OBJECT",
    "CL_INVALID_BUFFER_SIZE",
    "CL_INVALID_MIP_LEVEL",
    "CL_INVALID_GLOBAL_WORK_SIZE",
};

#define VERIFY(st, err) \
  printf("%s: %s\n", st, (-err >= 0 && -err < 64) ? error_string[-err] : ""); \
  assert(err == CL_SUCCESS)

opencl_environment *cl_init_gpu(void)
{
  cl_int err;
  opencl_environment *ev = (opencl_environment *) malloc(sizeof(opencl_environment));

  char buffer[1024];
  cl_uint num_platforms;

  printf("Initialize OpenCL object and context\n");
  //setup devices and context
  
  // Get the number of platforms available
  err = clGetPlatformIDs(0, NULL, &num_platforms);
  VERIFY("clGetPlatformIDs (get number of platforms)", err);
  if (num_platforms == 0) {
    printf("No OpenCL platform found!\n");
    abort();
  }

  // Get the IDs of the available platforms
  cl_platform_id* clPlatformIDs = (cl_platform_id*)malloc(num_platforms * sizeof(cl_platform_id));
  err = clGetPlatformIDs (num_platforms, clPlatformIDs, NULL);
  VERIFY("clGetPlatformIDs (create platform list)", err);

  // Print them
  printf("Available platforms:\n");
  for(int i = 0; i < num_platforms; ++i)
  {
    err = clGetPlatformInfo (clPlatformIDs[i], CL_PLATFORM_NAME, 1024, &buffer, NULL);
    if(err == CL_SUCCESS)
    {
      printf("platform %d: %s\n", i, buffer);
    }
  }

  printf("Which platform de you want to use ? ");
  int nbr;
  scanf("%d", &nbr);
  ev->platform = clPlatformIDs[nbr];
  
  // Get the number of GPU devices available to the platform
  // we should probably expose the device type to the user
  // the other common option is CL_DEVICE_TYPE_CPU
  err = clGetDeviceIDs(ev->platform, CL_DEVICE_TYPE_GPU, 0, NULL, &ev->numDevices);
  VERIFY("clGetDeviceIDs (get number of devices)", err);


  // Create the device list
  ev->devices = (cl_device_id *) malloc(sizeof(cl_device_id) * ev->numDevices);
  err = clGetDeviceIDs(ev->platform, CL_DEVICE_TYPE_GPU, ev->numDevices, ev->devices, NULL);
  VERIFY("clGetDeviceIDs (create device list)", err);
  printf("number of devices: %d\n", ev->numDevices);


  // Ccreate the context
  ev->context = clCreateContext(0, 1, ev->devices, NULL, NULL, &err);
  VERIFY("clCreateContext", err);

  // Just use the first available device
  ev->deviceUsed = 0;
  
  //clGetDeviceInfo (cl_device_id device, cl_device_info param_name,
  //size_t param_value_size, void *param_value, size_t *param_value_size_ret)
  //
  //CL_DEVICE_GLOBAL_MEM_SIZE
  //CL_DEVICE_MAX_COMPUTE_UNITS
  //CL_DEVICE_MAX_WORK_ITEM_DIMENSIONS
  //
  //CL_DEVICE_MAX_WORK_ITEM_SIZES
  //
  //CL_DEVICE_MAX_WORK_GROUP_SIZE
  //
  clGetDeviceInfo (ev->devices[ev->deviceUsed], CL_DEVICE_GLOBAL_MEM_SIZE, 
      sizeof(cl_ulong), &ev->max_global_mem_size, NULL);
  printf("max_global_mem_size: %lu\n", (unsigned long) ev->max_global_mem_size);

  clGetDeviceInfo (ev->devices[ev->deviceUsed], CL_DEVICE_MAX_COMPUTE_UNITS, 
      sizeof(cl_uint), &ev->max_compute_units, NULL);
  printf("max_compute_units: %u\n", ev->max_compute_units);

  clGetDeviceInfo (ev->devices[ev->deviceUsed], CL_DEVICE_MAX_WORK_ITEM_SIZES,
      sizeof(size_t), &ev->max_work_item_sizes, NULL);
  printf("max_work_item_sizes: %d\n", (int) ev->max_work_item_sizes);

  clGetDeviceInfo (ev->devices[ev->deviceUsed], CL_DEVICE_MAX_WORK_GROUP_SIZE,
      sizeof(cl_uint), &ev->max_work_group_size, NULL);
  printf("max_work_group_size: %d\n", (int) ev->max_work_group_size);
  
  //create the command queue we will use to execute OpenCL commands
  //command_queue = clCreateCommandQueue(context, devices[deviceUsed], CL_QUEUE_OUT_OF_ORDER_EXEC_MODE_ENABLE, &err);
  ev->command_queue = clCreateCommandQueue(ev->context, ev->devices[ev->deviceUsed], 0, &err);
  VERIFY("clCreateCommandQueue", err);

  return ev;
}

void cl_destroy(opencl_environment *ev)
{
  printf("Releasing OpenCL memory\n");

  if(ev->command_queue)
    clReleaseCommandQueue(ev->command_queue);
 
  //need to release any other OpenCL memory objects here
  //if(cl_data)
  //  clReleaseMemObject(cl_data);

  if(ev->context)
    clReleaseContext(ev->context);
  
  if(ev->devices)
    free(ev->devices);

  printf("OpenCL memory released\n");
}

#define STRINGIFY(A) #A
#define MAKE_STR(a) STRINGIFY(a)

cl_program cl_load_program(opencl_environment *ev, const char *include_path, 
                       const char *filename, const char *compile_flags)
{
  cl_int err;
  int pl;
  size_t program_length;
  cl_program program;

  printf("load the program\n");
  
  char *source;

  //CL_SOURCE_DIR is set in the CMakeLists.txt

  char tmp[200];
  //sprintf(tmp, "./%s", filename);

  FILE *f = fopen(filename, "r");

  if (!f) {
    fprintf(stderr, "Unable to open %s for reading\n", filename);
    return NULL;
  }

  fseek(f, 0, SEEK_END);
  pl = ftell(f);
  fseek(f, 0, SEEK_SET);

  source = malloc(pl+1);
  pl = fread(source, 1, pl, f);
  fclose(f);
  ((char*)source)[pl] = '\0';
  program_length = (size_t) pl;

  // create the program
  program = clCreateProgramWithSource(ev->context, 1,
                    (const char **) &source, &program_length, &err);
  VERIFY("clCreateProgramWithSource", err);

  //Free buffer
  free(source);

  /* BUILD SECTION */

  sprintf(tmp, "/%s %s", include_path, compile_flags);
  printf("include_path: %s\n", tmp);

  printf("building the program\n");
  err = clBuildProgram(program, 0, NULL, tmp, NULL, NULL);
  VERIFY("clBuildProgram", err);

 // We chose to show the details of the compilation whatever happens
//  if(err != CL_SUCCESS)
  if(1)
  {
    int end = 0;
    if(err != CL_SUCCESS)
      end = 1;

    cl_build_status build_status;
    err = clGetProgramBuildInfo(program, ev->devices[ev->deviceUsed], CL_PROGRAM_BUILD_STATUS, sizeof(cl_build_status), &build_status, NULL);

    char *build_log;
    size_t ret_val_size;
    err = clGetProgramBuildInfo(program, ev->devices[ev->deviceUsed], CL_PROGRAM_BUILD_LOG, 0, NULL, &ret_val_size);

    build_log = (char *) malloc(sizeof(char) * (ret_val_size+1));
    err = clGetProgramBuildInfo(program, ev->devices[ev->deviceUsed], CL_PROGRAM_BUILD_LOG, ret_val_size, build_log, NULL);
    build_log[ret_val_size] = '\0';
    printf("BUILD LOG: \n %s", build_log);

    if (end)
      exit(-1);
  }
  printf("program built\n");

  return program;
}

void enqueue_data()
{

}
