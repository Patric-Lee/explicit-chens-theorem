import PlattPointSubsetKernel
import PlattPointPackets.S2B000109
import PlattPointPackets.S2B000110
import PlattPointPackets.S2B000111
import PlattPointPackets.S2B000112
import PlattPointPackets.S2B000113
import PlattGlobalGrid.S7B000019
namespace ChenEffective.PlattWindow.PointCovers.S7B000019
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000109.points ++ ChenEffective.PlattWindow.PointPackets.S2B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000111.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000112.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000113.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000019.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000019.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000019
