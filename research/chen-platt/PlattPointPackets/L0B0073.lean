import PlattPointPacketKernel
import PlattPointPackets.S7B000122
import PlattPointPackets.S7B000123
import PlattPointPackets.S7B000124
import PlattPointPackets.S7B000125
import PlattPointPackets.S7B000126
import PlattPointPackets.S7B000127
import PlattPointPackets.S7B000128
import PlattPointPackets.S7B000129
import PlattPointPackets.S7B000130
import PlattPointPackets.S7B000131
import PlattPointPackets.S7B000132
import PlattPointPackets.S7B000133
import PlattPointPackets.S7B000134
import PlattPointPackets.S7B000135
import PlattPointPackets.S7B000136
import PlattPointPackets.S7B000137
import PlattPointPackets.S7B000138
import PlattPointPackets.S7B000139
import PlattPointPackets.S7B000140
import PlattPointPackets.S7B000141
import PlattPointPackets.S7B000142
import PlattPointPackets.S7B000143
import PlattPointPackets.S7B000144
import PlattPointPackets.S7B000145
import PlattPointPackets.S7B000146
import PlattPointPackets.S7B000147
import PlattPointPackets.S7B000148
import PlattPointPackets.S7B000149
import PlattPointPackets.S7B000150
import PlattPointPackets.S7B000151
import PlattPointPackets.S7B000152
import PlattPointPackets.S7B000153
namespace ChenEffective.PlattWindow.PointPackets.L0B0073
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000122.points ++ ChenEffective.PlattWindow.PointPackets.S7B000123.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000124.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000126.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000127.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000129.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000130.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000131.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000132.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000133.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000134.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000135.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000136.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000137.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000138.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000139.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000140.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000141.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000142.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000143.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000144.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000145.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000146.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000147.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000148.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000149.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000150.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000151.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000152.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000153.points)
theorem certified : PointChainCertificate 8379957248 114694116420661 114694505273845 8514174976 114889767497565 114890156463719 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S7B000122.certified) ChenEffective.PlattWindow.PointPackets.S7B000123.certified) ChenEffective.PlattWindow.PointPackets.S7B000124.certified) ChenEffective.PlattWindow.PointPackets.S7B000125.certified) ChenEffective.PlattWindow.PointPackets.S7B000126.certified) ChenEffective.PlattWindow.PointPackets.S7B000127.certified) ChenEffective.PlattWindow.PointPackets.S7B000128.certified) ChenEffective.PlattWindow.PointPackets.S7B000129.certified) ChenEffective.PlattWindow.PointPackets.S7B000130.certified) ChenEffective.PlattWindow.PointPackets.S7B000131.certified) ChenEffective.PlattWindow.PointPackets.S7B000132.certified) ChenEffective.PlattWindow.PointPackets.S7B000133.certified) ChenEffective.PlattWindow.PointPackets.S7B000134.certified) ChenEffective.PlattWindow.PointPackets.S7B000135.certified) ChenEffective.PlattWindow.PointPackets.S7B000136.certified) ChenEffective.PlattWindow.PointPackets.S7B000137.certified) ChenEffective.PlattWindow.PointPackets.S7B000138.certified) ChenEffective.PlattWindow.PointPackets.S7B000139.certified) ChenEffective.PlattWindow.PointPackets.S7B000140.certified) ChenEffective.PlattWindow.PointPackets.S7B000141.certified) ChenEffective.PlattWindow.PointPackets.S7B000142.certified) ChenEffective.PlattWindow.PointPackets.S7B000143.certified) ChenEffective.PlattWindow.PointPackets.S7B000144.certified) ChenEffective.PlattWindow.PointPackets.S7B000145.certified) ChenEffective.PlattWindow.PointPackets.S7B000146.certified) ChenEffective.PlattWindow.PointPackets.S7B000147.certified) ChenEffective.PlattWindow.PointPackets.S7B000148.certified) ChenEffective.PlattWindow.PointPackets.S7B000149.certified) ChenEffective.PlattWindow.PointPackets.S7B000150.certified) ChenEffective.PlattWindow.PointPackets.S7B000151.certified) ChenEffective.PlattWindow.PointPackets.S7B000152.certified) ChenEffective.PlattWindow.PointPackets.S7B000153.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0073
