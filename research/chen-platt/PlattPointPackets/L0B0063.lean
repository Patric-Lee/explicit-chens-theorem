import PlattPointPacketKernel
import PlattPointPackets.S6B000115
import PlattPointPackets.S6B000116
import PlattPointPackets.S6B000117
import PlattPointPackets.S6B000118
import PlattPointPackets.S6B000119
import PlattPointPackets.S6B000120
import PlattPointPackets.S6B000121
import PlattPointPackets.S6B000122
import PlattPointPackets.S6B000123
import PlattPointPackets.S6B000124
import PlattPointPackets.S6B000125
import PlattPointPackets.S6B000126
import PlattPointPackets.S6B000127
import PlattPointPackets.S6B000128
import PlattPointPackets.S6B000129
import PlattPointPackets.S6B000130
import PlattPointPackets.S6B000131
import PlattPointPackets.S6B000132
import PlattPointPackets.S6B000133
import PlattPointPackets.S6B000134
import PlattPointPackets.S6B000135
import PlattPointPackets.S6B000136
import PlattPointPackets.S6B000137
import PlattPointPackets.S6B000138
import PlattPointPackets.S6B000139
import PlattPointPackets.S6B000140
import PlattPointPackets.S6B000141
import PlattPointPackets.S6B000142
import PlattPointPackets.S6B000143
import PlattPointPackets.S6B000144
import PlattPointPackets.S6B000145
import PlattPointPackets.S6B000146
namespace ChenEffective.PlattWindow.PointPackets.L0B0063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000115.points ++ ChenEffective.PlattWindow.PointPackets.S6B000116.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000118.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000120.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000121.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000122.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000123.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000124.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000126.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000127.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000129.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000130.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000131.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000132.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000133.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000134.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000135.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000136.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000137.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000138.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000139.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000140.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000141.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000142.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000143.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000144.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000145.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000146.points)
theorem certified : PointChainCertificate 7039877120 112539287387914 112539675011482 7174094848 112773638050141 112774025806792 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S6B000115.certified) ChenEffective.PlattWindow.PointPackets.S6B000116.certified) ChenEffective.PlattWindow.PointPackets.S6B000117.certified) ChenEffective.PlattWindow.PointPackets.S6B000118.certified) ChenEffective.PlattWindow.PointPackets.S6B000119.certified) ChenEffective.PlattWindow.PointPackets.S6B000120.certified) ChenEffective.PlattWindow.PointPackets.S6B000121.certified) ChenEffective.PlattWindow.PointPackets.S6B000122.certified) ChenEffective.PlattWindow.PointPackets.S6B000123.certified) ChenEffective.PlattWindow.PointPackets.S6B000124.certified) ChenEffective.PlattWindow.PointPackets.S6B000125.certified) ChenEffective.PlattWindow.PointPackets.S6B000126.certified) ChenEffective.PlattWindow.PointPackets.S6B000127.certified) ChenEffective.PlattWindow.PointPackets.S6B000128.certified) ChenEffective.PlattWindow.PointPackets.S6B000129.certified) ChenEffective.PlattWindow.PointPackets.S6B000130.certified) ChenEffective.PlattWindow.PointPackets.S6B000131.certified) ChenEffective.PlattWindow.PointPackets.S6B000132.certified) ChenEffective.PlattWindow.PointPackets.S6B000133.certified) ChenEffective.PlattWindow.PointPackets.S6B000134.certified) ChenEffective.PlattWindow.PointPackets.S6B000135.certified) ChenEffective.PlattWindow.PointPackets.S6B000136.certified) ChenEffective.PlattWindow.PointPackets.S6B000137.certified) ChenEffective.PlattWindow.PointPackets.S6B000138.certified) ChenEffective.PlattWindow.PointPackets.S6B000139.certified) ChenEffective.PlattWindow.PointPackets.S6B000140.certified) ChenEffective.PlattWindow.PointPackets.S6B000141.certified) ChenEffective.PlattWindow.PointPackets.S6B000142.certified) ChenEffective.PlattWindow.PointPackets.S6B000143.certified) ChenEffective.PlattWindow.PointPackets.S6B000144.certified) ChenEffective.PlattWindow.PointPackets.S6B000145.certified) ChenEffective.PlattWindow.PointPackets.S6B000146.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0063
