package Image;

import java.awt.Image;
import java.awt.image.*;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;

//public static Image getImageFromArray(int[] pixels, int width, int height) {
//    BufferedImage image = new BufferedImage(width, height, BufferedImage.TYPE_INT_ARGB);
//    WritableRaster raster = (WritableRaster) image.getData();
//    raster.setPixels(0,0,width,height,pixels);
//    return image;
//}

public class Write_int {
	private final int maxid;
	private final int w,h;
	private final String name;
	private Integer nbreset = 0;
	private final int[] pixels;
	private int idx = 0;
	private boolean finished = false;

	public Write_int (String name,int w,int h) {
		this.name = name;
		this.maxid = h*w;
		this.w = w;
		this.h = h;
		this.pixels = new int[maxid];
	}
	public boolean step(int [] pixel) {
		if (!finished) {
			pixels[idx] = ((pixel[0] & 0xff) << 16) | ((pixel[1] & 0xff) << 8) | (pixel[2] & 0xff);
			idx = idx + 1;
			if (idx == maxid) {
				finished = true;
				try {
					DataBuffer b = new DataBufferInt(pixels,maxid);
					WritableRaster r = Raster.createPackedRaster(b, w, h, w,
							new int[] {0xFF0000, 0xFF00, 0xFF}, null);
				    //BufferedImage image = new BufferedImage(w, h, BufferedImage.TYPE_INT_RGB);
				    //image.setRGB(0, 0, w, h, pixels, 0, w);
					ColorModel cm = new DirectColorModel(32, 0xff0000, 0xff00, 0xff, 0);
					BufferedImage image = new BufferedImage(cm, r, false, null);
					ImageIO.write(image, "png", new File(name+"___"+ nbreset.toString()));
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
		return finished;
	}

	public void reset(){ idx=0;finished=false; nbreset++;}
}
