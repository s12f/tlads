from typing import List

class Event():
    def __init__(self, op_id: int, op_type: str, body = None) -> None:
        assert op_type in ["start", "end"]
        self.op_id = op_id
        self.op_type = op_type
        self.body = body

    def __str__(self) -> str:
        return f"({self.op_id}, {self.op_type})"

    def __repr__(self) -> str:
        return self.__str__()

class Point():
    def __init__(self, op_id: int, start_body, end_body) -> None:
        self.op_id = op_id
        self.start_body = start_body
        self.end_body = end_body

    def __str__(self) -> str:
        return f"({self.op_id}, {self.start_body}, {self.end_body})"

    def __repr__(self) -> str:
        return self.__str__()

def compute_sequential_histories(history: List[Event]) -> List[Point]:
    result = []
    points = {}

    ids = set()
    paired_history = []
    ended = {}
    # remove unpaired event and collect ids
    # e.g. [(1, start), (2, start), (3, start), (2, end), (1, end)]
    #   => [(1, start), (2, start), (2, end), (1, end)]
    for event in history[::-1]:
        if event.op_type == "start":
            # ignore unpaired
            if event.op_id not in ended:
                continue
            ev = ended.pop(event.op_id)
            ids.add(event.op_id)
            points[event.op_id] = Point(event.op_id, event.body, ev.body)
        else:
            assert event.op_id not in ids
            ended[event.op_id] = event
        paired_history.append(event)
    paired_history.reverse()
    if len(paired_history) < 2:
        return []
    print(f"paired_history: {paired_history}")

    # group by overlapped events
    # e.g. [(1, start), (2, start), (2, end), (1, end)]
    #   => [{1}, {1, 2}, {1}]
    groups = []
    overlapped_ids = set()
    for event in paired_history:
        if event.op_type == "start":
            overlapped_ids.add(event.op_id)
        else:
            overlapped_ids.remove(event.op_id)
        if len(overlapped_ids) > 0:
            groups.append(overlapped_ids.copy())
    print(f"groups: {groups}")

    # compute unique point
    # e.g. [{1}, {1, 2}, {1}]
    #   => [{1}, {2}], [{1, 2}], [{2}, {1}]
    abc = []
    for i in ids:
        for g in groups:
            pass
    return result

if __name__ == "__main__":
    history = [
            Event(1, "start"),
            Event(2, "start"),
            Event(3, "start"),
            Event(2, "end"),
            Event(1, "end") ]
    rs = compute_sequential_histories(history)
    print(f"rs: {rs}")
