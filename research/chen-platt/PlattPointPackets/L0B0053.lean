import PlattPointPacketKernel
import PlattPointPackets.S5B000108
import PlattPointPackets.S5B000109
import PlattPointPackets.S5B000110
import PlattPointPackets.S5B000111
import PlattPointPackets.S5B000112
import PlattPointPackets.S5B000113
import PlattPointPackets.S5B000114
import PlattPointPackets.S5B000115
import PlattPointPackets.S5B000116
import PlattPointPackets.S5B000117
import PlattPointPackets.S5B000118
import PlattPointPackets.S5B000119
import PlattPointPackets.S5B000120
import PlattPointPackets.S5B000121
import PlattPointPackets.S5B000122
import PlattPointPackets.S5B000123
import PlattPointPackets.S5B000124
import PlattPointPackets.S5B000125
import PlattPointPackets.S5B000126
import PlattPointPackets.S5B000127
import PlattPointPackets.S5B000128
import PlattPointPackets.S5B000129
import PlattPointPackets.S5B000130
import PlattPointPackets.S5B000131
import PlattPointPackets.S5B000132
import PlattPointPackets.S5B000133
import PlattPointPackets.S5B000134
import PlattPointPackets.S5B000135
import PlattPointPackets.S5B000136
import PlattPointPackets.S5B000137
import PlattPointPackets.S5B000138
import PlattPointPackets.S5B000139
namespace ChenEffective.PlattWindow.PointPackets.L0B0053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000108.points ++ ChenEffective.PlattWindow.PointPackets.S5B000109.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000111.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000112.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000113.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000114.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000115.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000116.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000118.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000120.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000121.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000122.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000123.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000124.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000126.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000127.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000129.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000130.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000131.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000132.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000133.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000134.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000135.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000136.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000137.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000138.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000139.points)
theorem certified : PointChainCertificate 5699796992 109905818299926 109906204416212 5834014720 110197278828891 110197665114262 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S5B000108.certified) ChenEffective.PlattWindow.PointPackets.S5B000109.certified) ChenEffective.PlattWindow.PointPackets.S5B000110.certified) ChenEffective.PlattWindow.PointPackets.S5B000111.certified) ChenEffective.PlattWindow.PointPackets.S5B000112.certified) ChenEffective.PlattWindow.PointPackets.S5B000113.certified) ChenEffective.PlattWindow.PointPackets.S5B000114.certified) ChenEffective.PlattWindow.PointPackets.S5B000115.certified) ChenEffective.PlattWindow.PointPackets.S5B000116.certified) ChenEffective.PlattWindow.PointPackets.S5B000117.certified) ChenEffective.PlattWindow.PointPackets.S5B000118.certified) ChenEffective.PlattWindow.PointPackets.S5B000119.certified) ChenEffective.PlattWindow.PointPackets.S5B000120.certified) ChenEffective.PlattWindow.PointPackets.S5B000121.certified) ChenEffective.PlattWindow.PointPackets.S5B000122.certified) ChenEffective.PlattWindow.PointPackets.S5B000123.certified) ChenEffective.PlattWindow.PointPackets.S5B000124.certified) ChenEffective.PlattWindow.PointPackets.S5B000125.certified) ChenEffective.PlattWindow.PointPackets.S5B000126.certified) ChenEffective.PlattWindow.PointPackets.S5B000127.certified) ChenEffective.PlattWindow.PointPackets.S5B000128.certified) ChenEffective.PlattWindow.PointPackets.S5B000129.certified) ChenEffective.PlattWindow.PointPackets.S5B000130.certified) ChenEffective.PlattWindow.PointPackets.S5B000131.certified) ChenEffective.PlattWindow.PointPackets.S5B000132.certified) ChenEffective.PlattWindow.PointPackets.S5B000133.certified) ChenEffective.PlattWindow.PointPackets.S5B000134.certified) ChenEffective.PlattWindow.PointPackets.S5B000135.certified) ChenEffective.PlattWindow.PointPackets.S5B000136.certified) ChenEffective.PlattWindow.PointPackets.S5B000137.certified) ChenEffective.PlattWindow.PointPackets.S5B000138.certified) ChenEffective.PlattWindow.PointPackets.S5B000139.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0053
