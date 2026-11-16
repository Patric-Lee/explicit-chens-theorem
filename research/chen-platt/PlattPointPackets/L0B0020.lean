import PlattPointPacketKernel
import PlattPointPackets.S1B000640
import PlattPointPackets.S1B000641
import PlattPointPackets.S1B000642
import PlattPointPackets.S1B000643
import PlattPointPackets.S1B000644
import PlattPointPackets.S1B000645
import PlattPointPackets.S1B000646
import PlattPointPackets.S1B000647
import PlattPointPackets.S1B000648
import PlattPointPackets.S2B000000
import PlattPointPackets.S2B000001
import PlattPointPackets.S2B000002
import PlattPointPackets.S2B000003
import PlattPointPackets.S2B000004
import PlattPointPackets.S2B000005
import PlattPointPackets.S2B000006
import PlattPointPackets.S2B000007
import PlattPointPackets.S2B000008
import PlattPointPackets.S2B000009
import PlattPointPackets.S2B000010
import PlattPointPackets.S2B000011
import PlattPointPackets.S2B000012
import PlattPointPackets.S2B000013
import PlattPointPackets.S2B000014
import PlattPointPackets.S2B000015
import PlattPointPackets.S2B000016
import PlattPointPackets.S2B000017
import PlattPointPackets.S2B000018
import PlattPointPackets.S2B000019
import PlattPointPackets.S2B000020
import PlattPointPackets.S2B000021
import PlattPointPackets.S2B000022
namespace ChenEffective.PlattWindow.PointPackets.L0B0020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S1B000640.points ++ ChenEffective.PlattWindow.PointPackets.S1B000641.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000642.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000643.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000644.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000645.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000646.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000647.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000648.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000022.points)
theorem certified : PointChainCertificate 1295777792 90704379302318 90704753083065 1411121152 91845917373446 91846292131553 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S1B000640.certified) ChenEffective.PlattWindow.PointPackets.S1B000641.certified) ChenEffective.PlattWindow.PointPackets.S1B000642.certified) ChenEffective.PlattWindow.PointPackets.S1B000643.certified) ChenEffective.PlattWindow.PointPackets.S1B000644.certified) ChenEffective.PlattWindow.PointPackets.S1B000645.certified) ChenEffective.PlattWindow.PointPackets.S1B000646.certified) ChenEffective.PlattWindow.PointPackets.S1B000647.certified) ChenEffective.PlattWindow.PointPackets.S1B000648.certified) ChenEffective.PlattWindow.PointPackets.S2B000000.certified) ChenEffective.PlattWindow.PointPackets.S2B000001.certified) ChenEffective.PlattWindow.PointPackets.S2B000002.certified) ChenEffective.PlattWindow.PointPackets.S2B000003.certified) ChenEffective.PlattWindow.PointPackets.S2B000004.certified) ChenEffective.PlattWindow.PointPackets.S2B000005.certified) ChenEffective.PlattWindow.PointPackets.S2B000006.certified) ChenEffective.PlattWindow.PointPackets.S2B000007.certified) ChenEffective.PlattWindow.PointPackets.S2B000008.certified) ChenEffective.PlattWindow.PointPackets.S2B000009.certified) ChenEffective.PlattWindow.PointPackets.S2B000010.certified) ChenEffective.PlattWindow.PointPackets.S2B000011.certified) ChenEffective.PlattWindow.PointPackets.S2B000012.certified) ChenEffective.PlattWindow.PointPackets.S2B000013.certified) ChenEffective.PlattWindow.PointPackets.S2B000014.certified) ChenEffective.PlattWindow.PointPackets.S2B000015.certified) ChenEffective.PlattWindow.PointPackets.S2B000016.certified) ChenEffective.PlattWindow.PointPackets.S2B000017.certified) ChenEffective.PlattWindow.PointPackets.S2B000018.certified) ChenEffective.PlattWindow.PointPackets.S2B000019.certified) ChenEffective.PlattWindow.PointPackets.S2B000020.certified) ChenEffective.PlattWindow.PointPackets.S2B000021.certified) ChenEffective.PlattWindow.PointPackets.S2B000022.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0020
