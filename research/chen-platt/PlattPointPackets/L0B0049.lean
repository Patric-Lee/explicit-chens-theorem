import PlattPointPacketKernel
import PlattPointPackets.S4B000293
import PlattPointPackets.S4B000294
import PlattPointPackets.S4B000295
import PlattPointPackets.S4B000296
import PlattPointPackets.S4B000297
import PlattPointPackets.S4B000298
import PlattPointPackets.S4B000299
import PlattPointPackets.S4B000300
import PlattPointPackets.S4B000301
import PlattPointPackets.S4B000302
import PlattPointPackets.S4B000303
import PlattPointPackets.S4B000304
import PlattPointPackets.S4B000305
import PlattPointPackets.S4B000306
import PlattPointPackets.S4B000307
import PlattPointPackets.S4B000308
import PlattPointPackets.S4B000309
import PlattPointPackets.S4B000310
import PlattPointPackets.S4B000311
import PlattPointPackets.S4B000312
import PlattPointPackets.S5B000000
import PlattPointPackets.S5B000001
import PlattPointPackets.S5B000002
import PlattPointPackets.S5B000003
import PlattPointPackets.S5B000004
import PlattPointPackets.S5B000005
import PlattPointPackets.S5B000006
import PlattPointPackets.S5B000007
import PlattPointPackets.S5B000008
import PlattPointPackets.S5B000009
import PlattPointPackets.S5B000010
import PlattPointPackets.S5B000011
namespace ChenEffective.PlattWindow.PointPackets.L0B0049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S4B000293.points ++ ChenEffective.PlattWindow.PointPackets.S4B000294.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000295.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000296.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000297.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000298.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000299.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000300.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000301.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000302.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000303.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000304.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000305.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000306.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000307.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000308.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000309.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000310.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000004.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000005.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000006.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000007.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000008.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000009.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000010.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000011.points)
theorem certified : PointChainCertificate 5165023232 108668556597044 108668941984969 5297143808 108986287299629 108986672876518 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S4B000293.certified) ChenEffective.PlattWindow.PointPackets.S4B000294.certified) ChenEffective.PlattWindow.PointPackets.S4B000295.certified) ChenEffective.PlattWindow.PointPackets.S4B000296.certified) ChenEffective.PlattWindow.PointPackets.S4B000297.certified) ChenEffective.PlattWindow.PointPackets.S4B000298.certified) ChenEffective.PlattWindow.PointPackets.S4B000299.certified) ChenEffective.PlattWindow.PointPackets.S4B000300.certified) ChenEffective.PlattWindow.PointPackets.S4B000301.certified) ChenEffective.PlattWindow.PointPackets.S4B000302.certified) ChenEffective.PlattWindow.PointPackets.S4B000303.certified) ChenEffective.PlattWindow.PointPackets.S4B000304.certified) ChenEffective.PlattWindow.PointPackets.S4B000305.certified) ChenEffective.PlattWindow.PointPackets.S4B000306.certified) ChenEffective.PlattWindow.PointPackets.S4B000307.certified) ChenEffective.PlattWindow.PointPackets.S4B000308.certified) ChenEffective.PlattWindow.PointPackets.S4B000309.certified) ChenEffective.PlattWindow.PointPackets.S4B000310.certified) ChenEffective.PlattWindow.PointPackets.S4B000311.certified) ChenEffective.PlattWindow.PointPackets.S4B000312.certified) ChenEffective.PlattWindow.PointPackets.S5B000000.certified) ChenEffective.PlattWindow.PointPackets.S5B000001.certified) ChenEffective.PlattWindow.PointPackets.S5B000002.certified) ChenEffective.PlattWindow.PointPackets.S5B000003.certified) ChenEffective.PlattWindow.PointPackets.S5B000004.certified) ChenEffective.PlattWindow.PointPackets.S5B000005.certified) ChenEffective.PlattWindow.PointPackets.S5B000006.certified) ChenEffective.PlattWindow.PointPackets.S5B000007.certified) ChenEffective.PlattWindow.PointPackets.S5B000008.certified) ChenEffective.PlattWindow.PointPackets.S5B000009.certified) ChenEffective.PlattWindow.PointPackets.S5B000010.certified) ChenEffective.PlattWindow.PointPackets.S5B000011.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0049
