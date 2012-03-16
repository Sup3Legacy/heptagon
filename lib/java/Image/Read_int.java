package Image;

import java.awt.image.Raster;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;



public class Read_int {
	private Raster img;
	private final int w;
	private final int h;
	private int x = 0;
	private int y = 0;

	public Read_int (String name) {
		File inputFile = new File(name);
		try {
			this.img = ImageIO.read(inputFile).getData();
		} catch (IOException e) {
			this.img = null;
			e.printStackTrace();
		}
		this.w = img.getWidth();
		this.h = img.getHeight();
	}
	public int[] step() {
		int [] pixel = img.getPixel(x, y, new int[3]);
		x = x + 1;
		if (x == w) {
			x = 0;
			if (y == h) y = 0;
			else y = y + 1;
		}
		return pixel;
	}
	public void reset(){ x=0; y=0; }
}
