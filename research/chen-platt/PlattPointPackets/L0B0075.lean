import PlattPointPacketKernel
import PlattPointPackets.S7B000186
import PlattPointPackets.S7B000187
import PlattPointPackets.S7B000188
import PlattPointPackets.S7B000189
import PlattPointPackets.S7B000190
import PlattPointPackets.S7B000191
import PlattPointPackets.S7B000192
import PlattPointPackets.S7B000193
import PlattPointPackets.S7B000194
import PlattPointPackets.S7B000195
import PlattPointPackets.S7B000196
import PlattPointPackets.S7B000197
import PlattPointPackets.S7B000198
import PlattPointPackets.S7B000199
import PlattPointPackets.S7B000200
import PlattPointPackets.S7B000201
import PlattPointPackets.S7B000202
import PlattPointPackets.S7B000203
import PlattPointPackets.S7B000204
import PlattPointPackets.S7B000205
import PlattPointPackets.S7B000206
import PlattPointPackets.S7B000207
import PlattPointPackets.S7B000208
import PlattPointPackets.S7B000209
import PlattPointPackets.S7B000210
import PlattPointPackets.S7B000211
import PlattPointPackets.S7B000212
import PlattPointPackets.S7B000213
import PlattPointPackets.S7B000214
import PlattPointPackets.S7B000215
import PlattPointPackets.S7B000216
import PlattPointPackets.S7B000217
namespace ChenEffective.PlattWindow.PointPackets.L0B0075
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def points : List PrimePoint := (((((((((((((((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000186.points ++ ChenEffective.PlattWindow.PointPackets.S7B000187.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000188.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000189.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000190.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000191.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000192.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000193.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000194.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000195.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000196.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000197.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000198.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000199.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000200.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000201.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000202.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000203.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000204.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000205.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000206.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000207.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000208.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000209.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000210.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000211.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000212.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000213.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000214.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000215.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000216.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000217.points)
theorem certified : PointChainCertificate 8648392704 115082270435770 115082659513537 8782610432 115271606006600 115271995194379 points := PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (PointChainCertificate.append (ChenEffective.PlattWindow.PointPackets.S7B000186.certified) ChenEffective.PlattWindow.PointPackets.S7B000187.certified) ChenEffective.PlattWindow.PointPackets.S7B000188.certified) ChenEffective.PlattWindow.PointPackets.S7B000189.certified) ChenEffective.PlattWindow.PointPackets.S7B000190.certified) ChenEffective.PlattWindow.PointPackets.S7B000191.certified) ChenEffective.PlattWindow.PointPackets.S7B000192.certified) ChenEffective.PlattWindow.PointPackets.S7B000193.certified) ChenEffective.PlattWindow.PointPackets.S7B000194.certified) ChenEffective.PlattWindow.PointPackets.S7B000195.certified) ChenEffective.PlattWindow.PointPackets.S7B000196.certified) ChenEffective.PlattWindow.PointPackets.S7B000197.certified) ChenEffective.PlattWindow.PointPackets.S7B000198.certified) ChenEffective.PlattWindow.PointPackets.S7B000199.certified) ChenEffective.PlattWindow.PointPackets.S7B000200.certified) ChenEffective.PlattWindow.PointPackets.S7B000201.certified) ChenEffective.PlattWindow.PointPackets.S7B000202.certified) ChenEffective.PlattWindow.PointPackets.S7B000203.certified) ChenEffective.PlattWindow.PointPackets.S7B000204.certified) ChenEffective.PlattWindow.PointPackets.S7B000205.certified) ChenEffective.PlattWindow.PointPackets.S7B000206.certified) ChenEffective.PlattWindow.PointPackets.S7B000207.certified) ChenEffective.PlattWindow.PointPackets.S7B000208.certified) ChenEffective.PlattWindow.PointPackets.S7B000209.certified) ChenEffective.PlattWindow.PointPackets.S7B000210.certified) ChenEffective.PlattWindow.PointPackets.S7B000211.certified) ChenEffective.PlattWindow.PointPackets.S7B000212.certified) ChenEffective.PlattWindow.PointPackets.S7B000213.certified) ChenEffective.PlattWindow.PointPackets.S7B000214.certified) ChenEffective.PlattWindow.PointPackets.S7B000215.certified) ChenEffective.PlattWindow.PointPackets.S7B000216.certified) ChenEffective.PlattWindow.PointPackets.S7B000217.certified
#print axioms certified
end ChenEffective.PlattWindow.PointPackets.L0B0075
