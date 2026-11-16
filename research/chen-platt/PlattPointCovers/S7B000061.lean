import PlattPointSubsetKernel
import PlattPointPackets.S2B000280
import PlattPointPackets.S2B000281
import PlattPointPackets.S2B000282
import PlattPointPackets.S2B000283
import PlattPointPackets.S2B000284
import PlattPointPackets.S2B000285
import PlattGlobalGrid.S7B000061
namespace ChenEffective.PlattWindow.PointCovers.S7B000061
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000280.points ++ ChenEffective.PlattWindow.PointPackets.S2B000281.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000282.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000283.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000284.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000285.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000061.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000061.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000061
