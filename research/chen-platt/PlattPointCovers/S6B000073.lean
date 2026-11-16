import PlattPointSubsetKernel
import PlattPointPackets.S1B000529
import PlattPointPackets.S1B000530
import PlattPointPackets.S1B000531
import PlattPointPackets.S1B000532
import PlattPointPackets.S1B000533
import PlattGlobalGrid.S6B000073
namespace ChenEffective.PlattWindow.PointCovers.S6B000073
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000529.points ++ ChenEffective.PlattWindow.PointPackets.S1B000530.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000531.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000532.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000533.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000073.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000073.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000073
