import PlattPointSubsetKernel
import PlattPointPackets.S2B000266
import PlattPointPackets.S2B000267
import PlattPointPackets.S2B000268
import PlattPointPackets.S2B000269
import PlattPointPackets.S2B000270
import PlattPointPackets.S2B000271
import PlattGlobalGrid.S7B000058
namespace ChenEffective.PlattWindow.PointCovers.S7B000058
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000266.points ++ ChenEffective.PlattWindow.PointPackets.S2B000267.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000268.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000269.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000270.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000271.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000058.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000058.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000058
