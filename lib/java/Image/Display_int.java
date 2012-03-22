package Image;

import java.awt.Graphics;
import java.awt.Panel;
import java.awt.image.BufferedImage;
import javax.swing.JFrame;
import javax.swing.JPanel;


public class Display_int {
	private final JFrame frame;
	private final ShowImage panel;
	
	private final int maxid;
	private final int w,h;
	private final int[] pixels;
	private int idx = 0;
	private boolean finished = false;
	
	public Display_int(String title, int w, int h){
		this.maxid = h*w;
		this.w = w;
		this.h = h;
		this.pixels = new int[maxid];
		
		frame = new JFrame(title);
		panel = new ShowImage(w, h);
		frame.getContentPane().add(panel);
		JFrame.setDefaultLookAndFeelDecorated(true);
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frame.setSize(w,h);
		frame.setVisible(true);
		
	}
	
	public boolean step(int [] pixel) {
		pixels[idx] = ((pixel[0] & 0xff) << 16) | ((pixel[1] & 0xff) << 8) | (pixel[2] & 0xff);
		idx = idx + 1;
		if (idx == maxid) {
			finished = true;
			idx = 0;
			panel.image.setRGB(0, 0, w, h, pixels, 0, w);
			panel.repaint();
		}
		else {
			finished = false;
		}
		return finished;
	}
	
	private class ShowImage extends JPanel {
		public BufferedImage  image;
		public ShowImage(int w, int h) {
			image = new BufferedImage(w, h, BufferedImage.TYPE_INT_RGB);
		}
		public void paintComponent(Graphics g) {
			g.drawImage(image, 0, 0, null);
		}
	}

	public void reset(){ idx=0; finished=false;}
}