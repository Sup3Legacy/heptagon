#ifndef HEPT_IMAGE_C
#define HEPT_IMAGE_C

typedef void * Image__image;

typedef struct Image__open_image_stream_mem
{
  int init;
  Image__image img;
} Image__open_image_stream_mem;

typedef struct Image__open_image_stream_out
{
  Image__image img;
} Image__open_image_stream_out;

void Image__open_image_stream_reset(Image__open_image_stream_mem *self);
void Image__open_image_stream_step(int param_index, int w, int h, int read,
                            Image__open_image_stream_out *out,
                            Image__open_image_stream_mem *self);

typedef struct Image__read_pixel_mem
{
} Image__read_pixel_mem;

typedef struct Image__read_pixel_out
{
  int r;
  int g;
  int b;
} Image__read_pixel_out;

void Image__read_pixel_reset(Image__read_pixel_mem *self);
void Image__read_pixel_step(Image__image img,
                            Image__read_pixel_out *out,
                            Image__read_pixel_mem *self);

typedef struct Image__write_pixel_mem
{
} Image__write_pixel_mem;

typedef struct Image__write_pixel_out
{
} Image__write_pixel_out;

void Image__write_pixel_reset(Image__write_pixel_mem *self);
void Image__write_pixel_step(Image__image img, int r, int g, int b,
                             Image__write_pixel_out *out,
                             Image__write_pixel_mem *self);

#endif
