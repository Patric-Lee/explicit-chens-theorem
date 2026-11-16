import PlattPointPacketKernel
import PlattPointPackets.S4B000101
import PlattPointPackets.S4B000102
import PlattPointPackets.S4B000103
import PlattPointPackets.S4B000104
import PlattPointPackets.S4B000105
import PlattPointPackets.S4B000106
import PlattPointPackets.S4B000107
import PlattPointPackets.S4B000108
import PlattPointPackets.S4B000109
import PlattPointPackets.S4B000110
import PlattPointPackets.S4B000111
import PlattPointPackets.S4B000112
import PlattPointPackets.S4B000113
import PlattPointPackets.S4B000114
import PlattPointPackets.S4B000115
import PlattPointPackets.S4B000116
import PlattPointPackets.S4B000117
import PlattPointPackets.S4B000118
import PlattPointPackets.S4B000119
import PlattPointPackets.S4B000120
import PlattPointPackets.S4B000121
import PlattPointPackets.S4B000122
import PlattPointPackets.S4B000123
import PlattPointPackets.S4B000124
import PlattPointPackets.S4B000125
import PlattPointPackets.S4B000126
import PlattPointPackets.S4B000127
import PlattPointPackets.S4B000128
import PlattPointPackets.S4B000129
import PlattPointPackets.S4B000130
import PlattPointPackets.S4B000131
import PlattPointPackets.S4B000132
namespace ChenEffective.PlattWindow.PointPackets.L0B0043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S4B000101.points ++ ChenEffective.PlattWindow.PointPackets.S4B000102.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000103.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000105.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000106.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000107.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000108.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000109.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000111.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000112.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000113.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000114.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000115.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000116.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000118.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000120.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000121.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000122.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000123.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000124.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000126.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000127.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000129.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000130.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000131.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000132.points)
theorem certified : PointChainCertificate 4359716864 106527237907664 106527621976811 4493934592 106911427214465 106911811526898 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S4B000101.certified) ChenEffective.PlattWindow.PointPackets.S4B000102.certified) ChenEffective.PlattWindow.PointPackets.S4B000103.certified) ChenEffective.PlattWindow.PointPackets.S4B000104.certified) ChenEffective.PlattWindow.PointPackets.S4B000105.certified) ChenEffective.PlattWindow.PointPackets.S4B000106.certified) ChenEffective.PlattWindow.PointPackets.S4B000107.certified) ChenEffective.PlattWindow.PointPackets.S4B000108.certified) ChenEffective.PlattWindow.PointPackets.S4B000109.certified) ChenEffective.PlattWindow.PointPackets.S4B000110.certified) ChenEffective.PlattWindow.PointPackets.S4B000111.certified) ChenEffective.PlattWindow.PointPackets.S4B000112.certified) ChenEffective.PlattWindow.PointPackets.S4B000113.certified) ChenEffective.PlattWindow.PointPackets.S4B000114.certified) ChenEffective.PlattWindow.PointPackets.S4B000115.certified) ChenEffective.PlattWindow.PointPackets.S4B000116.certified) ChenEffective.PlattWindow.PointPackets.S4B000117.certified) ChenEffective.PlattWindow.PointPackets.S4B000118.certified) ChenEffective.PlattWindow.PointPackets.S4B000119.certified) ChenEffective.PlattWindow.PointPackets.S4B000120.certified) ChenEffective.PlattWindow.PointPackets.S4B000121.certified) ChenEffective.PlattWindow.PointPackets.S4B000122.certified) ChenEffective.PlattWindow.PointPackets.S4B000123.certified) ChenEffective.PlattWindow.PointPackets.S4B000124.certified) ChenEffective.PlattWindow.PointPackets.S4B000125.certified) ChenEffective.PlattWindow.PointPackets.S4B000126.certified) ChenEffective.PlattWindow.PointPackets.S4B000127.certified) ChenEffective.PlattWindow.PointPackets.S4B000128.certified) ChenEffective.PlattWindow.PointPackets.S4B000129.certified) ChenEffective.PlattWindow.PointPackets.S4B000130.certified) ChenEffective.PlattWindow.PointPackets.S4B000131.certified) ChenEffective.PlattWindow.PointPackets.S4B000132.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0043
