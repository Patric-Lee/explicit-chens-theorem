import PlattPointSubsetKernel
import PlattPointPackets.S1B000555
import PlattPointPackets.S1B000556
import PlattPointPackets.S1B000557
import PlattPointPackets.S1B000558
import PlattPointPackets.S1B000559
import PlattGlobalGrid.S6B000079
namespace ChenEffective.PlattWindow.PointCovers.S6B000079
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000555.points ++ ChenEffective.PlattWindow.PointPackets.S1B000556.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000557.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000558.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000559.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000079.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000079.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000079
