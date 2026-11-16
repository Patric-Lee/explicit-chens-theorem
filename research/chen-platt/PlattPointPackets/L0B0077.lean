import PlattPointPacketKernel
import PlattPointPackets.S7B000250
import PlattPointPackets.S7B000251
import PlattPointPackets.S7B000252
import PlattPointPackets.S7B000253
import PlattPointPackets.S7B000254
import PlattPointPackets.S7B000255
import PlattPointPackets.S7B000256
import PlattPointPackets.S7B000257
import PlattPointPackets.S7B000258
import PlattPointPackets.S7B000259
import PlattPointPackets.S7B000260
import PlattPointPackets.S7B000261
import PlattPointPackets.S7B000262
import PlattPointPackets.S7B000263
import PlattPointPackets.S7B000264
import PlattPointPackets.S7B000265
import PlattPointPackets.S7B000266
import PlattPointPackets.S7B000267
import PlattPointPackets.S7B000268
import PlattPointPackets.S7B000269
import PlattPointPackets.S7B000270
import PlattPointPackets.S7B000271
import PlattPointPackets.S7B000272
import PlattPointPackets.S7B000273
import PlattPointPackets.S7B000274
import PlattPointPackets.S7B000275
import PlattPointPackets.S7B000276
import PlattPointPackets.S7B000277
import PlattPointPackets.S7B000278
import PlattPointPackets.S7B000279
import PlattPointPackets.S7B000280
import PlattPointPackets.S7B000281
namespace ChenEffective.PlattWindow.PointPackets.L0B0077
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000250.points ++ ChenEffective.PlattWindow.PointPackets.S7B000251.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000252.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000253.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000254.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000255.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000256.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000257.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000258.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000259.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000260.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000261.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000262.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000263.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000264.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000265.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000266.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000267.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000268.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000269.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000270.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000271.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000272.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000273.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000274.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000275.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000276.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000277.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000278.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000279.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000280.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000281.points)
theorem certified : PointChainCertificate 8916828160 115457996874821 115458386171407 9051045888 115641497483261 115641886887179 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S7B000250.certified) ChenEffective.PlattWindow.PointPackets.S7B000251.certified) ChenEffective.PlattWindow.PointPackets.S7B000252.certified) ChenEffective.PlattWindow.PointPackets.S7B000253.certified) ChenEffective.PlattWindow.PointPackets.S7B000254.certified) ChenEffective.PlattWindow.PointPackets.S7B000255.certified) ChenEffective.PlattWindow.PointPackets.S7B000256.certified) ChenEffective.PlattWindow.PointPackets.S7B000257.certified) ChenEffective.PlattWindow.PointPackets.S7B000258.certified) ChenEffective.PlattWindow.PointPackets.S7B000259.certified) ChenEffective.PlattWindow.PointPackets.S7B000260.certified) ChenEffective.PlattWindow.PointPackets.S7B000261.certified) ChenEffective.PlattWindow.PointPackets.S7B000262.certified) ChenEffective.PlattWindow.PointPackets.S7B000263.certified) ChenEffective.PlattWindow.PointPackets.S7B000264.certified) ChenEffective.PlattWindow.PointPackets.S7B000265.certified) ChenEffective.PlattWindow.PointPackets.S7B000266.certified) ChenEffective.PlattWindow.PointPackets.S7B000267.certified) ChenEffective.PlattWindow.PointPackets.S7B000268.certified) ChenEffective.PlattWindow.PointPackets.S7B000269.certified) ChenEffective.PlattWindow.PointPackets.S7B000270.certified) ChenEffective.PlattWindow.PointPackets.S7B000271.certified) ChenEffective.PlattWindow.PointPackets.S7B000272.certified) ChenEffective.PlattWindow.PointPackets.S7B000273.certified) ChenEffective.PlattWindow.PointPackets.S7B000274.certified) ChenEffective.PlattWindow.PointPackets.S7B000275.certified) ChenEffective.PlattWindow.PointPackets.S7B000276.certified) ChenEffective.PlattWindow.PointPackets.S7B000277.certified) ChenEffective.PlattWindow.PointPackets.S7B000278.certified) ChenEffective.PlattWindow.PointPackets.S7B000279.certified) ChenEffective.PlattWindow.PointPackets.S7B000280.certified) ChenEffective.PlattWindow.PointPackets.S7B000281.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0077
