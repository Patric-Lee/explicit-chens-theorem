import PlattPointPacketKernel
import PlattPointPackets.S5B000300
import PlattPointPackets.S5B000301
import PlattPointPackets.S5B000302
import PlattPointPackets.S5B000303
import PlattPointPackets.S5B000304
import PlattPointPackets.S5B000305
import PlattPointPackets.S5B000306
import PlattPointPackets.S5B000307
import PlattPointPackets.S5B000308
import PlattPointPackets.S5B000309
import PlattPointPackets.S5B000310
import PlattPointPackets.S5B000311
import PlattPointPackets.S5B000312
import PlattPointPackets.S6B000000
import PlattPointPackets.S6B000001
import PlattPointPackets.S6B000002
import PlattPointPackets.S6B000003
import PlattPointPackets.S6B000004
import PlattPointPackets.S6B000005
import PlattPointPackets.S6B000006
import PlattPointPackets.S6B000007
import PlattPointPackets.S6B000008
import PlattPointPackets.S6B000009
import PlattPointPackets.S6B000010
import PlattPointPackets.S6B000011
import PlattPointPackets.S6B000012
import PlattPointPackets.S6B000013
import PlattPointPackets.S6B000014
import PlattPointPackets.S6B000015
import PlattPointPackets.S6B000016
import PlattPointPackets.S6B000017
import PlattPointPackets.S6B000018
namespace ChenEffective.PlattWindow.PointPackets.L0B0059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000300.points ++ ChenEffective.PlattWindow.PointPackets.S5B000301.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000302.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000303.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000304.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000305.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000306.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000307.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000308.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000309.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000310.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000011.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000012.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000013.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000014.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000015.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000016.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000017.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000018.points)
theorem certified : PointChainCertificate 6505103360 111556830122301 111557217187371 6637223936 111807260315453 111807647523051 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S5B000300.certified) ChenEffective.PlattWindow.PointPackets.S5B000301.certified) ChenEffective.PlattWindow.PointPackets.S5B000302.certified) ChenEffective.PlattWindow.PointPackets.S5B000303.certified) ChenEffective.PlattWindow.PointPackets.S5B000304.certified) ChenEffective.PlattWindow.PointPackets.S5B000305.certified) ChenEffective.PlattWindow.PointPackets.S5B000306.certified) ChenEffective.PlattWindow.PointPackets.S5B000307.certified) ChenEffective.PlattWindow.PointPackets.S5B000308.certified) ChenEffective.PlattWindow.PointPackets.S5B000309.certified) ChenEffective.PlattWindow.PointPackets.S5B000310.certified) ChenEffective.PlattWindow.PointPackets.S5B000311.certified) ChenEffective.PlattWindow.PointPackets.S5B000312.certified) ChenEffective.PlattWindow.PointPackets.S6B000000.certified) ChenEffective.PlattWindow.PointPackets.S6B000001.certified) ChenEffective.PlattWindow.PointPackets.S6B000002.certified) ChenEffective.PlattWindow.PointPackets.S6B000003.certified) ChenEffective.PlattWindow.PointPackets.S6B000004.certified) ChenEffective.PlattWindow.PointPackets.S6B000005.certified) ChenEffective.PlattWindow.PointPackets.S6B000006.certified) ChenEffective.PlattWindow.PointPackets.S6B000007.certified) ChenEffective.PlattWindow.PointPackets.S6B000008.certified) ChenEffective.PlattWindow.PointPackets.S6B000009.certified) ChenEffective.PlattWindow.PointPackets.S6B000010.certified) ChenEffective.PlattWindow.PointPackets.S6B000011.certified) ChenEffective.PlattWindow.PointPackets.S6B000012.certified) ChenEffective.PlattWindow.PointPackets.S6B000013.certified) ChenEffective.PlattWindow.PointPackets.S6B000014.certified) ChenEffective.PlattWindow.PointPackets.S6B000015.certified) ChenEffective.PlattWindow.PointPackets.S6B000016.certified) ChenEffective.PlattWindow.PointPackets.S6B000017.certified) ChenEffective.PlattWindow.PointPackets.S6B000018.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0059
