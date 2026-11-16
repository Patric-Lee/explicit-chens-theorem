import PlattPointPacketKernel
import PlattPointPackets.S7B000282
import PlattPointPackets.S7B000283
import PlattPointPackets.S7B000284
import PlattPointPackets.S7B000285
import PlattPointPackets.S7B000286
import PlattPointPackets.S7B000287
import PlattPointPackets.S7B000288
import PlattPointPackets.S7B000289
import PlattPointPackets.S7B000290
import PlattPointPackets.S7B000291
import PlattPointPackets.S7B000292
import PlattPointPackets.S7B000293
import PlattPointPackets.S7B000294
import PlattPointPackets.S7B000295
import PlattPointPackets.S7B000296
import PlattPointPackets.S7B000297
import PlattPointPackets.S7B000298
import PlattPointPackets.S7B000299
import PlattPointPackets.S7B000300
import PlattPointPackets.S7B000301
import PlattPointPackets.S7B000302
import PlattPointPackets.S7B000303
import PlattPointPackets.S7B000304
import PlattPointPackets.S7B000305
import PlattPointPackets.S7B000306
import PlattPointPackets.S7B000307
import PlattPointPackets.S7B000308
import PlattPointPackets.S7B000309
import PlattPointPackets.S7B000310
import PlattPointPackets.S7B000311
import PlattPointPackets.S7B000312
import PlattPointPackets.S8B000000
namespace ChenEffective.PlattWindow.PointPackets.L0B0078
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000282.points ++ ChenEffective.PlattWindow.PointPackets.S7B000283.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000284.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000285.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000286.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000287.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000288.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000289.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000290.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000291.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000292.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000293.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000294.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000295.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000296.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000297.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000298.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000299.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000300.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000301.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000302.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000303.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000304.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000305.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000306.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000307.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000308.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000309.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000310.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000000.points)
theorem certified : PointChainCertificate 9051045888 115641497483261 115641886887179 9183166464 115819334242089 115819723750598 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S7B000282.certified) ChenEffective.PlattWindow.PointPackets.S7B000283.certified) ChenEffective.PlattWindow.PointPackets.S7B000284.certified) ChenEffective.PlattWindow.PointPackets.S7B000285.certified) ChenEffective.PlattWindow.PointPackets.S7B000286.certified) ChenEffective.PlattWindow.PointPackets.S7B000287.certified) ChenEffective.PlattWindow.PointPackets.S7B000288.certified) ChenEffective.PlattWindow.PointPackets.S7B000289.certified) ChenEffective.PlattWindow.PointPackets.S7B000290.certified) ChenEffective.PlattWindow.PointPackets.S7B000291.certified) ChenEffective.PlattWindow.PointPackets.S7B000292.certified) ChenEffective.PlattWindow.PointPackets.S7B000293.certified) ChenEffective.PlattWindow.PointPackets.S7B000294.certified) ChenEffective.PlattWindow.PointPackets.S7B000295.certified) ChenEffective.PlattWindow.PointPackets.S7B000296.certified) ChenEffective.PlattWindow.PointPackets.S7B000297.certified) ChenEffective.PlattWindow.PointPackets.S7B000298.certified) ChenEffective.PlattWindow.PointPackets.S7B000299.certified) ChenEffective.PlattWindow.PointPackets.S7B000300.certified) ChenEffective.PlattWindow.PointPackets.S7B000301.certified) ChenEffective.PlattWindow.PointPackets.S7B000302.certified) ChenEffective.PlattWindow.PointPackets.S7B000303.certified) ChenEffective.PlattWindow.PointPackets.S7B000304.certified) ChenEffective.PlattWindow.PointPackets.S7B000305.certified) ChenEffective.PlattWindow.PointPackets.S7B000306.certified) ChenEffective.PlattWindow.PointPackets.S7B000307.certified) ChenEffective.PlattWindow.PointPackets.S7B000308.certified) ChenEffective.PlattWindow.PointPackets.S7B000309.certified) ChenEffective.PlattWindow.PointPackets.S7B000310.certified) ChenEffective.PlattWindow.PointPackets.S7B000311.certified) ChenEffective.PlattWindow.PointPackets.S7B000312.certified) ChenEffective.PlattWindow.PointPackets.S8B000000.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0078
