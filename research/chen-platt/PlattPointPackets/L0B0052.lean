import PlattPointPacketKernel
import PlattPointPackets.S5B000076
import PlattPointPackets.S5B000077
import PlattPointPackets.S5B000078
import PlattPointPackets.S5B000079
import PlattPointPackets.S5B000080
import PlattPointPackets.S5B000081
import PlattPointPackets.S5B000082
import PlattPointPackets.S5B000083
import PlattPointPackets.S5B000084
import PlattPointPackets.S5B000085
import PlattPointPackets.S5B000086
import PlattPointPackets.S5B000087
import PlattPointPackets.S5B000088
import PlattPointPackets.S5B000089
import PlattPointPackets.S5B000090
import PlattPointPackets.S5B000091
import PlattPointPackets.S5B000092
import PlattPointPackets.S5B000093
import PlattPointPackets.S5B000094
import PlattPointPackets.S5B000095
import PlattPointPackets.S5B000096
import PlattPointPackets.S5B000097
import PlattPointPackets.S5B000098
import PlattPointPackets.S5B000099
import PlattPointPackets.S5B000100
import PlattPointPackets.S5B000101
import PlattPointPackets.S5B000102
import PlattPointPackets.S5B000103
import PlattPointPackets.S5B000104
import PlattPointPackets.S5B000105
import PlattPointPackets.S5B000106
import PlattPointPackets.S5B000107
namespace ChenEffective.PlattWindow.PointPackets.L0B0052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000076.points ++ ChenEffective.PlattWindow.PointPackets.S5B000077.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000078.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000080.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000081.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000082.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000083.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000084.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000085.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000086.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000087.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000088.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000089.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000090.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000091.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000092.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000093.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000094.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000095.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000096.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000097.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000098.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000099.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000100.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000101.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000102.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000103.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000105.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000106.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000107.points)
theorem certified : PointChainCertificate 5565579264 109606991956824 109607377899032 5699796992 109905818299926 109906204416212 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S5B000076.certified) ChenEffective.PlattWindow.PointPackets.S5B000077.certified) ChenEffective.PlattWindow.PointPackets.S5B000078.certified) ChenEffective.PlattWindow.PointPackets.S5B000079.certified) ChenEffective.PlattWindow.PointPackets.S5B000080.certified) ChenEffective.PlattWindow.PointPackets.S5B000081.certified) ChenEffective.PlattWindow.PointPackets.S5B000082.certified) ChenEffective.PlattWindow.PointPackets.S5B000083.certified) ChenEffective.PlattWindow.PointPackets.S5B000084.certified) ChenEffective.PlattWindow.PointPackets.S5B000085.certified) ChenEffective.PlattWindow.PointPackets.S5B000086.certified) ChenEffective.PlattWindow.PointPackets.S5B000087.certified) ChenEffective.PlattWindow.PointPackets.S5B000088.certified) ChenEffective.PlattWindow.PointPackets.S5B000089.certified) ChenEffective.PlattWindow.PointPackets.S5B000090.certified) ChenEffective.PlattWindow.PointPackets.S5B000091.certified) ChenEffective.PlattWindow.PointPackets.S5B000092.certified) ChenEffective.PlattWindow.PointPackets.S5B000093.certified) ChenEffective.PlattWindow.PointPackets.S5B000094.certified) ChenEffective.PlattWindow.PointPackets.S5B000095.certified) ChenEffective.PlattWindow.PointPackets.S5B000096.certified) ChenEffective.PlattWindow.PointPackets.S5B000097.certified) ChenEffective.PlattWindow.PointPackets.S5B000098.certified) ChenEffective.PlattWindow.PointPackets.S5B000099.certified) ChenEffective.PlattWindow.PointPackets.S5B000100.certified) ChenEffective.PlattWindow.PointPackets.S5B000101.certified) ChenEffective.PlattWindow.PointPackets.S5B000102.certified) ChenEffective.PlattWindow.PointPackets.S5B000103.certified) ChenEffective.PlattWindow.PointPackets.S5B000104.certified) ChenEffective.PlattWindow.PointPackets.S5B000105.certified) ChenEffective.PlattWindow.PointPackets.S5B000106.certified) ChenEffective.PlattWindow.PointPackets.S5B000107.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0052
