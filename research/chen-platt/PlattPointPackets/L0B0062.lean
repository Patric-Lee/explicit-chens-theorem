import PlattPointPacketKernel
import PlattPointPackets.S6B000083
import PlattPointPackets.S6B000084
import PlattPointPackets.S6B000085
import PlattPointPackets.S6B000086
import PlattPointPackets.S6B000087
import PlattPointPackets.S6B000088
import PlattPointPackets.S6B000089
import PlattPointPackets.S6B000090
import PlattPointPackets.S6B000091
import PlattPointPackets.S6B000092
import PlattPointPackets.S6B000093
import PlattPointPackets.S6B000094
import PlattPointPackets.S6B000095
import PlattPointPackets.S6B000096
import PlattPointPackets.S6B000097
import PlattPointPackets.S6B000098
import PlattPointPackets.S6B000099
import PlattPointPackets.S6B000100
import PlattPointPackets.S6B000101
import PlattPointPackets.S6B000102
import PlattPointPackets.S6B000103
import PlattPointPackets.S6B000104
import PlattPointPackets.S6B000105
import PlattPointPackets.S6B000106
import PlattPointPackets.S6B000107
import PlattPointPackets.S6B000108
import PlattPointPackets.S6B000109
import PlattPointPackets.S6B000110
import PlattPointPackets.S6B000111
import PlattPointPackets.S6B000112
import PlattPointPackets.S6B000113
import PlattPointPackets.S6B000114
namespace ChenEffective.PlattWindow.PointPackets.L0B0062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000083.points ++ ChenEffective.PlattWindow.PointPackets.S6B000084.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000085.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000086.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000087.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000088.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000089.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000090.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000091.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000092.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000093.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000094.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000095.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000096.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000097.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000098.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000099.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000100.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000101.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000102.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000103.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000105.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000106.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000107.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000108.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000109.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000111.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000112.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000113.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000114.points)
theorem certified : PointChainCertificate 6905659392 112300249760691 112300637248566 7039877120 112539287387914 112539675011482 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S6B000083.certified) ChenEffective.PlattWindow.PointPackets.S6B000084.certified) ChenEffective.PlattWindow.PointPackets.S6B000085.certified) ChenEffective.PlattWindow.PointPackets.S6B000086.certified) ChenEffective.PlattWindow.PointPackets.S6B000087.certified) ChenEffective.PlattWindow.PointPackets.S6B000088.certified) ChenEffective.PlattWindow.PointPackets.S6B000089.certified) ChenEffective.PlattWindow.PointPackets.S6B000090.certified) ChenEffective.PlattWindow.PointPackets.S6B000091.certified) ChenEffective.PlattWindow.PointPackets.S6B000092.certified) ChenEffective.PlattWindow.PointPackets.S6B000093.certified) ChenEffective.PlattWindow.PointPackets.S6B000094.certified) ChenEffective.PlattWindow.PointPackets.S6B000095.certified) ChenEffective.PlattWindow.PointPackets.S6B000096.certified) ChenEffective.PlattWindow.PointPackets.S6B000097.certified) ChenEffective.PlattWindow.PointPackets.S6B000098.certified) ChenEffective.PlattWindow.PointPackets.S6B000099.certified) ChenEffective.PlattWindow.PointPackets.S6B000100.certified) ChenEffective.PlattWindow.PointPackets.S6B000101.certified) ChenEffective.PlattWindow.PointPackets.S6B000102.certified) ChenEffective.PlattWindow.PointPackets.S6B000103.certified) ChenEffective.PlattWindow.PointPackets.S6B000104.certified) ChenEffective.PlattWindow.PointPackets.S6B000105.certified) ChenEffective.PlattWindow.PointPackets.S6B000106.certified) ChenEffective.PlattWindow.PointPackets.S6B000107.certified) ChenEffective.PlattWindow.PointPackets.S6B000108.certified) ChenEffective.PlattWindow.PointPackets.S6B000109.certified) ChenEffective.PlattWindow.PointPackets.S6B000110.certified) ChenEffective.PlattWindow.PointPackets.S6B000111.certified) ChenEffective.PlattWindow.PointPackets.S6B000112.certified) ChenEffective.PlattWindow.PointPackets.S6B000113.certified) ChenEffective.PlattWindow.PointPackets.S6B000114.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0062
