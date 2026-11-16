import PlattPointPacketKernel
import PlattPointPackets.S6B000307
import PlattPointPackets.S6B000308
import PlattPointPackets.S6B000309
import PlattPointPackets.S6B000310
import PlattPointPackets.S6B000311
import PlattPointPackets.S6B000312
import PlattPointPackets.S7B000000
import PlattPointPackets.S7B000001
import PlattPointPackets.S7B000002
import PlattPointPackets.S7B000003
import PlattPointPackets.S7B000004
import PlattPointPackets.S7B000005
import PlattPointPackets.S7B000006
import PlattPointPackets.S7B000007
import PlattPointPackets.S7B000008
import PlattPointPackets.S7B000009
import PlattPointPackets.S7B000010
import PlattPointPackets.S7B000011
import PlattPointPackets.S7B000012
import PlattPointPackets.S7B000013
import PlattPointPackets.S7B000014
import PlattPointPackets.S7B000015
import PlattPointPackets.S7B000016
import PlattPointPackets.S7B000017
import PlattPointPackets.S7B000018
import PlattPointPackets.S7B000019
import PlattPointPackets.S7B000020
import PlattPointPackets.S7B000021
import PlattPointPackets.S7B000022
import PlattPointPackets.S7B000023
import PlattPointPackets.S7B000024
import PlattPointPackets.S7B000025
namespace ChenEffective.PlattWindow.PointPackets.L0B0069
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000307.points ++ ChenEffective.PlattWindow.PointPackets.S6B000308.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000309.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000310.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000023.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000025.points)
theorem certified : PointChainCertificate 7845183488 113880530269649 113880918656150 7977304064 114086779467393 114087167971777 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S6B000307.certified) ChenEffective.PlattWindow.PointPackets.S6B000308.certified) ChenEffective.PlattWindow.PointPackets.S6B000309.certified) ChenEffective.PlattWindow.PointPackets.S6B000310.certified) ChenEffective.PlattWindow.PointPackets.S6B000311.certified) ChenEffective.PlattWindow.PointPackets.S6B000312.certified) ChenEffective.PlattWindow.PointPackets.S7B000000.certified) ChenEffective.PlattWindow.PointPackets.S7B000001.certified) ChenEffective.PlattWindow.PointPackets.S7B000002.certified) ChenEffective.PlattWindow.PointPackets.S7B000003.certified) ChenEffective.PlattWindow.PointPackets.S7B000004.certified) ChenEffective.PlattWindow.PointPackets.S7B000005.certified) ChenEffective.PlattWindow.PointPackets.S7B000006.certified) ChenEffective.PlattWindow.PointPackets.S7B000007.certified) ChenEffective.PlattWindow.PointPackets.S7B000008.certified) ChenEffective.PlattWindow.PointPackets.S7B000009.certified) ChenEffective.PlattWindow.PointPackets.S7B000010.certified) ChenEffective.PlattWindow.PointPackets.S7B000011.certified) ChenEffective.PlattWindow.PointPackets.S7B000012.certified) ChenEffective.PlattWindow.PointPackets.S7B000013.certified) ChenEffective.PlattWindow.PointPackets.S7B000014.certified) ChenEffective.PlattWindow.PointPackets.S7B000015.certified) ChenEffective.PlattWindow.PointPackets.S7B000016.certified) ChenEffective.PlattWindow.PointPackets.S7B000017.certified) ChenEffective.PlattWindow.PointPackets.S7B000018.certified) ChenEffective.PlattWindow.PointPackets.S7B000019.certified) ChenEffective.PlattWindow.PointPackets.S7B000020.certified) ChenEffective.PlattWindow.PointPackets.S7B000021.certified) ChenEffective.PlattWindow.PointPackets.S7B000022.certified) ChenEffective.PlattWindow.PointPackets.S7B000023.certified) ChenEffective.PlattWindow.PointPackets.S7B000024.certified) ChenEffective.PlattWindow.PointPackets.S7B000025.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0069
