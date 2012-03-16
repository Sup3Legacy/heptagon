package Image;

import java.awt.image.BufferedImage;
import java.awt.image.RenderedImage;
import java.awt.image.WritableRaster;
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
	private final WritableRaster img;
	private final int w;
	private final int h;
	private final String name;
	private Integer nbreset = 0;
	private int x = 0;
	private int y = 0;
	private boolean finished = false;

	public Write_int (String name,int w,int h) {
		BufferedImage image = new BufferedImage(w, h, BufferedImage.TYPE_INT_RGB);
		this.name = name;
		this.img = (WritableRaster) image.getData();
		this.w = img.getWidth();
		this.h = img.getHeight();
	}
	public boolean step(int [] pixel) {
		if (!finished) {
			img.setPixel(x, y, pixel);
			x = x + 1;
			if (x == w) {
				x = 0;
				if (y == h) {
					finished = true;
					try {
						ImageIO.write((RenderedImage) img, "png",
								new File(name+"___"+ nbreset.toString()));
					} catch (IOException e) {
						e.printStackTrace();
					}
					y = 0;
				}
				else y = y + 1;
			}
		}
		return finished;
	}

	public void reset(){ x=0;y=0;finished=false; nbreset++;}
}
