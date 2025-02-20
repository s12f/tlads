# Cache: Write-Through Pattern

Implement and verify the Write-Through caching strategy in TLA+.

Assumptions:
    - All reads and writes go through a single cache to the database.
    - Single-session connection for each key range between the cache and database.

Guarantees:
    - Linearizability(Strong consistency)
