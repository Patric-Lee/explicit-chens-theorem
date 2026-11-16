import PlattPointPacketKernel
import PlattPointPackets.S3B000286
import PlattPointPackets.S3B000287
import PlattPointPackets.S3B000288
import PlattPointPackets.S3B000289
import PlattPointPackets.S3B000290
import PlattPointPackets.S3B000291
import PlattPointPackets.S3B000292
import PlattPointPackets.S3B000293
import PlattPointPackets.S3B000294
import PlattPointPackets.S3B000295
import PlattPointPackets.S3B000296
import PlattPointPackets.S3B000297
import PlattPointPackets.S3B000298
import PlattPointPackets.S3B000299
import PlattPointPackets.S3B000300
import PlattPointPackets.S3B000301
import PlattPointPackets.S3B000302
import PlattPointPackets.S3B000303
import PlattPointPackets.S3B000304
import PlattPointPackets.S3B000305
import PlattPointPackets.S3B000306
import PlattPointPackets.S3B000307
import PlattPointPackets.S3B000308
import PlattPointPackets.S3B000309
import PlattPointPackets.S3B000310
import PlattPointPackets.S3B000311
import PlattPointPackets.S3B000312
import PlattPointPackets.S4B000000
import PlattPointPackets.S4B000001
import PlattPointPackets.S4B000002
import PlattPointPackets.S4B000003
import PlattPointPackets.S4B000004
namespace ChenEffective.PlattWindow.PointPackets.L0B0039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S3B000286.points ++ ChenEffective.PlattWindow.PointPackets.S3B000287.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000288.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000289.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000290.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000291.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000292.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000293.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000294.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000295.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000296.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000297.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000298.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000299.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000300.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000301.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000302.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000303.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000304.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000305.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000306.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000307.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000308.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000309.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000310.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S3B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000003.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000004.points)
theorem certified : PointChainCertificate 3824943104 104862877653381 104863260769809 3957063680 105295690457495 105296073816827 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S3B000286.certified) ChenEffective.PlattWindow.PointPackets.S3B000287.certified) ChenEffective.PlattWindow.PointPackets.S3B000288.certified) ChenEffective.PlattWindow.PointPackets.S3B000289.certified) ChenEffective.PlattWindow.PointPackets.S3B000290.certified) ChenEffective.PlattWindow.PointPackets.S3B000291.certified) ChenEffective.PlattWindow.PointPackets.S3B000292.certified) ChenEffective.PlattWindow.PointPackets.S3B000293.certified) ChenEffective.PlattWindow.PointPackets.S3B000294.certified) ChenEffective.PlattWindow.PointPackets.S3B000295.certified) ChenEffective.PlattWindow.PointPackets.S3B000296.certified) ChenEffective.PlattWindow.PointPackets.S3B000297.certified) ChenEffective.PlattWindow.PointPackets.S3B000298.certified) ChenEffective.PlattWindow.PointPackets.S3B000299.certified) ChenEffective.PlattWindow.PointPackets.S3B000300.certified) ChenEffective.PlattWindow.PointPackets.S3B000301.certified) ChenEffective.PlattWindow.PointPackets.S3B000302.certified) ChenEffective.PlattWindow.PointPackets.S3B000303.certified) ChenEffective.PlattWindow.PointPackets.S3B000304.certified) ChenEffective.PlattWindow.PointPackets.S3B000305.certified) ChenEffective.PlattWindow.PointPackets.S3B000306.certified) ChenEffective.PlattWindow.PointPackets.S3B000307.certified) ChenEffective.PlattWindow.PointPackets.S3B000308.certified) ChenEffective.PlattWindow.PointPackets.S3B000309.certified) ChenEffective.PlattWindow.PointPackets.S3B000310.certified) ChenEffective.PlattWindow.PointPackets.S3B000311.certified) ChenEffective.PlattWindow.PointPackets.S3B000312.certified) ChenEffective.PlattWindow.PointPackets.S4B000000.certified) ChenEffective.PlattWindow.PointPackets.S4B000001.certified) ChenEffective.PlattWindow.PointPackets.S4B000002.certified) ChenEffective.PlattWindow.PointPackets.S4B000003.certified) ChenEffective.PlattWindow.PointPackets.S4B000004.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0039
