import PlattPointSubsetKernel
import PlattPointPackets.S2B000077
import PlattPointPackets.S2B000078
import PlattPointPackets.S2B000079
import PlattPointPackets.S2B000080
import PlattGlobalGrid.S7B000009
namespace ChenEffective.PlattWindow.PointCovers.S7B000009
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000077.points ++ ChenEffective.PlattWindow.PointPackets.S2B000078.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000080.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000009.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000009.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000009
