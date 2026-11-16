import PlattPointSubsetKernel
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
import PlattGlobalGrid.S8B000099
namespace ChenEffective.PlattWindow.PointCovers.S8B000099
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000193.points ++ ChenEffective.PlattWindow.PointPackets.S7B000194.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000195.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000196.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000197.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000198.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000199.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000200.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000201.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000202.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000203.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000204.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000205.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000206.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000207.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000208.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000209.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000099.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000099.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000099
