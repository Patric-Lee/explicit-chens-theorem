import PlattPointSubsetKernel
import PlattPointPackets.S2B000113
import PlattPointPackets.S2B000114
import PlattPointPackets.S2B000115
import PlattPointPackets.S2B000116
import PlattGlobalGrid.S7B000020
namespace ChenEffective.PlattWindow.PointCovers.S7B000020
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000113.points ++ ChenEffective.PlattWindow.PointPackets.S2B000114.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000115.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000116.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000020.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000020.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000020
