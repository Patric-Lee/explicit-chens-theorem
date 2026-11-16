import PlattPointSubsetKernel
import PlattPointPackets.S4B000193
import PlattPointPackets.S4B000194
import PlattPointPackets.S4B000195
import PlattPointPackets.S4B000196
import PlattPointPackets.S4B000197
import PlattPointPackets.S4B000198
import PlattPointPackets.S4B000199
import PlattPointPackets.S4B000200
import PlattPointPackets.S4B000201
import PlattPointPackets.S4B000202
import PlattGlobalGrid.S8B000024
namespace ChenEffective.PlattWindow.PointCovers.S8B000024
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000193.points ++ ChenEffective.PlattWindow.PointPackets.S4B000194.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000195.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000196.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000197.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000198.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000199.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000200.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000201.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000202.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000024.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000024.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000024
