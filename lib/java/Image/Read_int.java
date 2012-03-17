package Image;

import java.awt.image.BufferedImage;
import java.awt.image.Raster;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;



public class Read_int {
	private int[] pixels;
	private final int maxid;
	private int idx = 0;

	public Read_int (String name) {
		File inputFile = new File(name);
		BufferedImage img = null;
		try {
			img = ImageIO.read(inputFile);
		} catch (IOException e) {
			e.printStackTrace();
		}
		int w = img.getWidth();
		int h = img.getHeight();
		this.maxid = w*h;
		pixels = new int[w * h];
		img.getRGB(0, 0, w, h, pixels, 0, w);
		System.out.printf("maxid %d",maxid);
	}
	public int[] step() {
		int [] pixel = new int[] {(pixels[idx] >> 16) & 0xff,(pixels[idx] >> 8) & 0xff,(pixels[idx] & 0xff)};
		idx = idx + 1;
		if (idx >= maxid)
			idx = 0;
		return pixel;
	}
	public void reset(){ idx=0; }
}
