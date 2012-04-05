extern "C" {
#include "image.h"
#include <sys/stat.h>
}

#include "CImg.h"

using namespace cimg_library;

extern "C" int global_argc;
extern "C" char **global_argv;

typedef struct
{
  CImg<int> *image;
  char *filename;
  int x;
  int y;
  int w;
  int h;
} internal_image;

extern "C" void Image__open_image_stream_reset(
  Image__open_image_stream_mem *self
  )
{
  if(self->init && self->img)
  {
    internal_image *iimg = reinterpret_cast<internal_image *>(self->img);
    if(iimg->image)
      delete iimg->image;
    delete iimg;
    self->img = 0;
  }
  self->init = 0;
}

extern "C" void Image__open_image_stream_step(
  int param_index, int w, int h, int read,
  Image__open_image_stream_out *out,
  Image__open_image_stream_mem *self
  )
{
  if(self->init == 0)
  {
    if(param_index < 0 || param_index + 1 >= global_argc)
    {
      fprintf(stderr, "Not enough command-line arguments\n", global_argc);
      exit(1);
    }

    internal_image *iimg = new internal_image;
    struct stat st;

    iimg->filename = global_argv[param_index + 1];

    if(read)
    {
      if(stat(iimg->filename, &st) != 0)
      {
        fprintf(stderr, "Unknown file %s\n", iimg->filename);
        exit(1);
      }
      printf("Loading image file %s\n", iimg->filename);
      iimg->image = new CImg<int>(iimg->filename);

      if(iimg->image->width() != w || iimg->image->height() != h)
      {
        fprintf(stderr,
                "Bad dimensions for %s: %dx%d, expected %dx%d\n",
                iimg->filename,
                iimg->image->width(), iimg->image->height(), w, h);
        exit(1);
      }
    }
    else
    {
      printf("Creating image file %s\n", iimg->filename);
      iimg->image = new CImg<int>(w, h, 1, 3, 0);
    }

    iimg->x = 0;
    iimg->y = 0;
    iimg->w = iimg->image->width();
    iimg->h = iimg->image->height();

    self->img = reinterpret_cast<void *>(iimg);

    self->init = 1;
  }

  out->img = self->img;
}

extern "C" void Image__read_pixel_reset(Image__read_pixel_mem *self)
{
}

extern "C" void Image__read_pixel_step(Image__image img,
                                       Image__read_pixel_out *out,
                                       Image__read_pixel_mem *self)
{
  internal_image *iimg = reinterpret_cast<internal_image *>(img);
  out->r = (*iimg->image)(iimg->x, iimg->y, 0, 0);
  out->g = (*iimg->image)(iimg->x, iimg->y, 0, 1);
  out->b = (*iimg->image)(iimg->x, iimg->y, 0, 2);

  if(++iimg->x == iimg->w)
  {
    iimg->x = 0;
    if(++iimg->y == iimg->h)
      iimg->y = 0;
  }
}

extern "C" void Image__write_pixel_reset(Image__write_pixel_mem *self)
{
}

extern "C" void Image__write_pixel_step(Image__image img, int r, int g, int b,
                                        Image__write_pixel_out *out,
                                        Image__write_pixel_mem *self)
{
  internal_image *iimg = reinterpret_cast<internal_image *>(img);
  (*iimg->image)(iimg->x, iimg->y, 0, 0) = r;
  (*iimg->image)(iimg->x, iimg->y, 0, 1) = g;
  (*iimg->image)(iimg->x, iimg->y, 0, 2) = b;

  if(++iimg->x == iimg->w)
  {
    iimg->x = 0;
    if(++iimg->y == iimg->h)
    {
      printf("Saving %s\n", iimg->filename);
      iimg->y = 0;
      iimg->image->save(iimg->filename);
    }
  }
}
