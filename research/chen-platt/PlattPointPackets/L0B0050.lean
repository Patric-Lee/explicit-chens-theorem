import PlattPointPacketKernel
import PlattPointPackets.S5B000012
import PlattPointPackets.S5B000013
import PlattPointPackets.S5B000014
import PlattPointPackets.S5B000015
import PlattPointPackets.S5B000016
import PlattPointPackets.S5B000017
import PlattPointPackets.S5B000018
import PlattPointPackets.S5B000019
import PlattPointPackets.S5B000020
import PlattPointPackets.S5B000021
import PlattPointPackets.S5B000022
import PlattPointPackets.S5B000023
import PlattPointPackets.S5B000024
import PlattPointPackets.S5B000025
import PlattPointPackets.S5B000026
import PlattPointPackets.S5B000027
import PlattPointPackets.S5B000028
import PlattPointPackets.S5B000029
import PlattPointPackets.S5B000030
import PlattPointPackets.S5B000031
import PlattPointPackets.S5B000032
import PlattPointPackets.S5B000033
import PlattPointPackets.S5B000034
import PlattPointPackets.S5B000035
import PlattPointPackets.S5B000036
import PlattPointPackets.S5B000037
import PlattPointPackets.S5B000038
import PlattPointPackets.S5B000039
import PlattPointPackets.S5B000040
import PlattPointPackets.S5B000041
import PlattPointPackets.S5B000042
import PlattPointPackets.S5B000043
namespace ChenEffective.PlattWindow.PointPackets.L0B0050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000012.points ++ ChenEffective.PlattWindow.PointPackets.S5B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000023.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000026.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000029.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000030.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000031.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000032.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000033.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000034.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000035.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000036.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000037.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000038.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000039.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000040.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000041.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000042.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000043.points)
theorem certified : PointChainCertificate 5297143808 108986287299629 108986672876518 5431361536 109300610935765 109300996698290 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S5B000012.certified) ChenEffective.PlattWindow.PointPackets.S5B000013.certified) ChenEffective.PlattWindow.PointPackets.S5B000014.certified) ChenEffective.PlattWindow.PointPackets.S5B000015.certified) ChenEffective.PlattWindow.PointPackets.S5B000016.certified) ChenEffective.PlattWindow.PointPackets.S5B000017.certified) ChenEffective.PlattWindow.PointPackets.S5B000018.certified) ChenEffective.PlattWindow.PointPackets.S5B000019.certified) ChenEffective.PlattWindow.PointPackets.S5B000020.certified) ChenEffective.PlattWindow.PointPackets.S5B000021.certified) ChenEffective.PlattWindow.PointPackets.S5B000022.certified) ChenEffective.PlattWindow.PointPackets.S5B000023.certified) ChenEffective.PlattWindow.PointPackets.S5B000024.certified) ChenEffective.PlattWindow.PointPackets.S5B000025.certified) ChenEffective.PlattWindow.PointPackets.S5B000026.certified) ChenEffective.PlattWindow.PointPackets.S5B000027.certified) ChenEffective.PlattWindow.PointPackets.S5B000028.certified) ChenEffective.PlattWindow.PointPackets.S5B000029.certified) ChenEffective.PlattWindow.PointPackets.S5B000030.certified) ChenEffective.PlattWindow.PointPackets.S5B000031.certified) ChenEffective.PlattWindow.PointPackets.S5B000032.certified) ChenEffective.PlattWindow.PointPackets.S5B000033.certified) ChenEffective.PlattWindow.PointPackets.S5B000034.certified) ChenEffective.PlattWindow.PointPackets.S5B000035.certified) ChenEffective.PlattWindow.PointPackets.S5B000036.certified) ChenEffective.PlattWindow.PointPackets.S5B000037.certified) ChenEffective.PlattWindow.PointPackets.S5B000038.certified) ChenEffective.PlattWindow.PointPackets.S5B000039.certified) ChenEffective.PlattWindow.PointPackets.S5B000040.certified) ChenEffective.PlattWindow.PointPackets.S5B000041.certified) ChenEffective.PlattWindow.PointPackets.S5B000042.certified) ChenEffective.PlattWindow.PointPackets.S5B000043.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0050
