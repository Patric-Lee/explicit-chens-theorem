import PlattPointSubsetKernel
import PlattPointPackets.S1B000550
import PlattPointPackets.S1B000551
import PlattPointPackets.S1B000552
import PlattPointPackets.S1B000553
import PlattPointPackets.S1B000554
import PlattPointPackets.S1B000555
import PlattGlobalGrid.S6B000078
namespace ChenEffective.PlattWindow.PointCovers.S6B000078
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S1B000550.points ++ ChenEffective.PlattWindow.PointPackets.S1B000551.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000552.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000553.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000554.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000555.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000078.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000078.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000078
