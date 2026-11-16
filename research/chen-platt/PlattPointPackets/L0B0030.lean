import PlattPointPacketKernel
import PlattPointPackets.S2B000311
import PlattPointPackets.S2B000312
import PlattPointPackets.S3B000000
import PlattPointPackets.S3B000001
import PlattPointPackets.S3B000002
import PlattPointPackets.S3B000003
import PlattPointPackets.S3B000004
import PlattPointPackets.S3B000005
import PlattPointPackets.S3B000006
import PlattPointPackets.S3B000007
import PlattPointPackets.S3B000008
import PlattPointPackets.S3B000009
import PlattPointPackets.S3B000010
import PlattPointPackets.S3B000011
import PlattPointPackets.S3B000012
import PlattPointPackets.S3B000013
import PlattPointPackets.S3B000014
import PlattPointPackets.S3B000015
import PlattPointPackets.S3B000016
import PlattPointPackets.S3B000017
import PlattPointPackets.S3B000018
import PlattPointPackets.S3B000019
import PlattPointPackets.S3B000020
import PlattPointPackets.S3B000021
import PlattPointPackets.S3B000022
import PlattPointPackets.S3B000023
import PlattPointPackets.S3B000024
import PlattPointPackets.S3B000025
import PlattPointPackets.S3B000026
import PlattPointPackets.S3B000027
import PlattPointPackets.S3B000028
import PlattPointPackets.S3B000029
namespace ChenEffective.PlattWindow.PointPackets.L0B0030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S2B000311.points ++ ChenEffective.PlattWindow.PointPackets.S2B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000018.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000019.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000020.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000021.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000022.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000023.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000024.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000025.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000026.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000027.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000028.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000029.points)
theorem certified : PointChainCertificate 2619080704 99989726586931 99990106938394 2751201280 100627662507767 100628043231717 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S2B000311.certified) ChenEffective.PlattWindow.PointPackets.S2B000312.certified) ChenEffective.PlattWindow.PointPackets.S3B000000.certified) ChenEffective.PlattWindow.PointPackets.S3B000001.certified) ChenEffective.PlattWindow.PointPackets.S3B000002.certified) ChenEffective.PlattWindow.PointPackets.S3B000003.certified) ChenEffective.PlattWindow.PointPackets.S3B000004.certified) ChenEffective.PlattWindow.PointPackets.S3B000005.certified) ChenEffective.PlattWindow.PointPackets.S3B000006.certified) ChenEffective.PlattWindow.PointPackets.S3B000007.certified) ChenEffective.PlattWindow.PointPackets.S3B000008.certified) ChenEffective.PlattWindow.PointPackets.S3B000009.certified) ChenEffective.PlattWindow.PointPackets.S3B000010.certified) ChenEffective.PlattWindow.PointPackets.S3B000011.certified) ChenEffective.PlattWindow.PointPackets.S3B000012.certified) ChenEffective.PlattWindow.PointPackets.S3B000013.certified) ChenEffective.PlattWindow.PointPackets.S3B000014.certified) ChenEffective.PlattWindow.PointPackets.S3B000015.certified) ChenEffective.PlattWindow.PointPackets.S3B000016.certified) ChenEffective.PlattWindow.PointPackets.S3B000017.certified) ChenEffective.PlattWindow.PointPackets.S3B000018.certified) ChenEffective.PlattWindow.PointPackets.S3B000019.certified) ChenEffective.PlattWindow.PointPackets.S3B000020.certified) ChenEffective.PlattWindow.PointPackets.S3B000021.certified) ChenEffective.PlattWindow.PointPackets.S3B000022.certified) ChenEffective.PlattWindow.PointPackets.S3B000023.certified) ChenEffective.PlattWindow.PointPackets.S3B000024.certified) ChenEffective.PlattWindow.PointPackets.S3B000025.certified) ChenEffective.PlattWindow.PointPackets.S3B000026.certified) ChenEffective.PlattWindow.PointPackets.S3B000027.certified) ChenEffective.PlattWindow.PointPackets.S3B000028.certified) ChenEffective.PlattWindow.PointPackets.S3B000029.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0030
