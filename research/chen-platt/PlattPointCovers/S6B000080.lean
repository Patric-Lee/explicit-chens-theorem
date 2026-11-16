import PlattPointSubsetKernel
import PlattPointPackets.S1B000559
import PlattPointPackets.S1B000560
import PlattPointPackets.S1B000561
import PlattPointPackets.S1B000562
import PlattPointPackets.S1B000563
import PlattGlobalGrid.S6B000080
namespace ChenEffective.PlattWindow.PointCovers.S6B000080
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000559.points ++ ChenEffective.PlattWindow.PointPackets.S1B000560.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000561.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000562.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000563.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000080.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000080.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000080
