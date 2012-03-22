package Image;

import java.awt.image.BufferedImage;
import java.awt.image.Raster;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;



public class Read_int {
	
	private final String name;
	private int maxid;
	private int[] pixels;
	private int idx = 0;

	private int _read_file() {
		File inputFile = new File(name);
		BufferedImage img = null;
		try {
			img = ImageIO.read(inputFile);
		} catch (IOException e) {
			e.printStackTrace();
		}
		int w = img.getWidth();
		int h = img.getHeight();
		int maxid = w*h;
		pixels = new int[maxid];
		img.getRGB(0, 0, w, h, pixels, 0, w);
		return maxid;
	}
	
	public Read_int (String name) {
		this.name = name;
		this.idx = 0;
		this.maxid = _read_file();
	}
	public int[] step() {
		int [] pixel = new int[] {(pixels[idx] >> 16) & 0xff,(pixels[idx] >> 8) & 0xff,(pixels[idx] & 0xff)};
		idx = idx + 1;
		if (idx >= maxid)
			idx = 0;
		return pixel;
	}
	public void reset(){
		this.idx = 0;
		this.maxid = _read_file(); }
}
