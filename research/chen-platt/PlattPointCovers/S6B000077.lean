import PlattPointSubsetKernel
import PlattPointPackets.S1B000546
import PlattPointPackets.S1B000547
import PlattPointPackets.S1B000548
import PlattPointPackets.S1B000549
import PlattPointPackets.S1B000550
import PlattGlobalGrid.S6B000077
namespace ChenEffective.PlattWindow.PointCovers.S6B000077
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000546.points ++ ChenEffective.PlattWindow.PointPackets.S1B000547.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000548.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000549.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000550.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000077.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000077.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000077
